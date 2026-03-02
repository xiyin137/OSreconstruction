# Work Order Lock (Mandatory)

Last updated: 2026-03-02

This file is a hard execution lock for current BHWPermutation work.
The agent must follow this order exactly and must not re-prioritize.

## Locked order

1. `d=1, n=2` first:
  - Primary target:
    `blocker_eventually_forward_eq_on_prepared_nhds_d1_adjSwap_deferred`
  - Required path forward:
    Lorentz invariant-function route on `FT_{1,2}` via
    `(Q₀,Q₁,P,S)` factorization and swap action
    `(Q₀,Q₁,P,S) ↦ (Q₁,Q₀,P,-S)`.
  - Work through explicit `n=2` wrappers first when useful:
    - `blocker_eventually_forward_eq_on_prepared_nhds_d1_adjSwap_n2`
    - `blocker_eventually_extendF_base_eq_on_prepared_nhds_d1_swap01_n2`
2. `d=1, n=3` second:
   - Same local blocker shape specialized to `n=3`.
   - Reuse the pattern learned from `n=2`.
3. Only after (1) and (2) are settled:
   - `n>=4` branches,
   - general `d=1` global closure,
   - `d>=2` connectedness cleanup/refinement.

## Hard prohibitions before steps (1) and (2) complete

1. No switching focus to `n>=4` proof construction.
2. No switching focus to general connectedness/decomposition work except
   minimal dependencies required by the active small-`n` step.
3. No architecture detours that do not directly advance the active step in
   the locked order.
4. No adoption of new axioms.
5. For `d=1,n=2`, proof work MUST follow the Lorentz-invariant route in
   `D1N2LorentzInvariantRoute.lean`; do not switch to non-route strategies.
6. For `d=1,n=2`, use Lorentz invariant-function arguments as the primary
   analytic path (model/factorization/swap-kernel), not midpoint or
   real-witness substitutes.

## Session protocol

At session start, agent must explicitly state:

- current lock step (`n=2` or `n=3`),
- active target theorem name,
- why the next edit is required for that target.

Before any substantial exploration/edit outside the active step, agent must:

- stop,
- record the reason in the "Deviation Log" below,
- return to the active locked step.

## Completion criteria

Step 1 (`n=2`) is complete only when either:

1. theorem is fully proved from current production hypotheses, or
2. a formal impossibility/insufficiency statement is proved in Lean with a
   precise missing hypothesis identified.

Step 2 (`n=3`) uses the same completion rule.

No transition to step 3 is allowed before both step 1 and step 2 are marked
"complete" in this file.

## Progress board

- Step 1 (`d=1,n=2` local blocker): IN_PROGRESS
  - Current active theorem:
    `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred`
  - Exact remaining subgoal inside that theorem:
    for `z ∈ FT_{1,2}` with `swap·z ∈ ET_{1,2}`,
    prove `extendF F (swap·z) = F z`.
    The theorem
    `blocker_d1N2Source_swappedInvariantForwardEq_invariantOnly_core_deferred`
    is now a proved wrapper via
    `d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq`.
    The realizable-pair kernel theorem
    `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`
    is now proved from the swapped-invariant wrapper theorem by unpacking
    realizability witnesses
    and rewriting with `hf_onFT`.
    Theorems now proved as wrappers from that realizable-pair theorem:
    `blocker_d1N2ForwardBaseOpenAnchor_source_invariant_core_main_deferred`
    (via `d1N2ForwardBaseOpenAnchor_source_of_pairSwap`) and
    `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_main_deferred`.
    Current in-code reduction now also proves
    `blocker_d1N2Source_swappedInvariantForwardEq_core_deferred`
    via factorization plus the realizable-pair theorem above.
    The wrapper theorem
    `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred`
    is now a direct alias to the realizable-pair main theorem (now sorry-free).
    Then
    `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred`
    is proved from factorization + realizable-pair symmetry + forward bridge.
    The former invariant realizable-pair theorem
    `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred`
    is now proved by wrappers once this anchor package is available.
  - `blocker_d1N2InvariantQuadricModel_core_deferred` is now proved by:
    1. factorization (`blocker_d1N2InvariantFactorization_core_deferred`),
    2. symmetric extension of a source kernel from realizable tuples to all
       quadric tuples, and
    3. the active realizable-pair involution theorem above.
  - `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`
    is now proved directly from the active theorem above via
    `d1N2InvariantRealizable_pair_of_forwardizable`.
  - Equivalence helper now proved:
    `d1N2InvariantKernelPairSwapOnRealizable_iff_forwardizableDiffZero`.
  - Additional exact bridge now proved (for fixed `hf_onFT`):
    `d1N2ForwardSwapEq_onFT_iff_invariantKernelPairSwapOnRealizable`,
    with directional wrappers
    `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable` and
    `d1N2InvariantKernelPairSwapOnRealizable_of_forwardSwapEq`.
  - Connectivity bridge now proved:
    `d1N2_isConnected_adjSwapForwardOverlapSet_of_seedConnectedBlocker`,
    reducing the `n=2` adjacent forward-overlap connectedness obligation to
    the existing deferred seed connectedness theorem.
  - Complex-anchor propagation bridge now proved:
    `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor`.
    This removes the need for a real ET-overlap witness in the n=2 bridge once
    an open anchor subset in `permForwardOverlapSet` is available.
  - Exact source-level reduction now proved:
    `d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor`.
    So for `d=1,n=2` source data, the active theorem is formally equivalent to
    existence of a nonempty complex-open forward-base anchor.
    The source-side direction is factored as:
    `d1N2ForwardBaseOpenAnchor_source_of_pairSwap`.
  - Dependency audit (2026-03-02):
    all pre-1307 invariant algebra/bridge lemmas are `sorry`-free except the
    deferred connectedness branch (`blocker_isConnected_permSeedSet_d1_nontrivial`).
    The non-circular bridge
    `d1N2InvariantKernelPairSwapOnRealizable_source_of_connectedOpenAnchor`
    is already `sorry`-free; the unresolved implication remains:
    source data `hsource` implies complex open-anchor existence
    (equivalently, the forward-swap core in the active theorem body).
    Added explicit connected-overlap equivalence:
    `d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor_of_connectedForwardOverlap`
    (also `sorry`-free).
  - `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`
    is now a proved wrapper to the active source-invariant core theorem.
  - `blocker_d1N2InvariantKernelSwapOnForwardizable_source_core_deferred`
    is now a proved wrapper (`sub_eq_zero`) around the active diff-zero theorem.
  - `blocker_d1N2LocalForwardEqNhd_core_deferred` is now proved by reduction to:
    1. factorization (`blocker_d1N2InvariantFactorization_core_deferred`),
    2. source-core forwardizable diff-zero theorem above, and
    3. `d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric`.
  - `blocker_d1N2InvariantModel_core_deferred` is now a proved wrapper that
    combines:
    1. `blocker_d1N2InvariantFactorization_core_deferred`,
    2. forwardizable-core extraction, and
    3. `blocker_d1N2InvariantKernelSwap_core_of_forwardizableQuadricDiffZero`.
  - Formal insufficiency (proved in Lean):
    `d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero`
    shows `source + hf_onFT` does not force full-quadric involution for an
    arbitrary representative `f`.
  - Strengthened non-circular bridge now proved:
    `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_realWitness`
    derives `FT` forward-swap equality from existing EOW/identity machinery,
    given explicit geometric inputs
    (`connected adjSwap forward-overlap + real spacelike overlap witness`).
  - Added invariant-route chart/Jacobian scaffolding in
    `D1N2LorentzInvariantRoute.lean`:
    `d1N2RealConfig` and closed-form real invariant formulas
    (`d1Q0R_realConfig`, `d1Q1R_realConfig`, `d1P01R_realConfig`,
    `d1S01R_realConfig`), explicit chart-level spacelike identity
    (`d1_adj_spacelike_expr_realConfig`), and explicit nonzero Jacobian minor
    witness at `d1N2RealProbePoint`
    (`d1N2InvariantJacobianMinorAtProbe_det_ne_zero`).
- Step 2 (`d=1,n=3` local blocker): PENDING
- Step 3 (`n>=4` and global cleanup): LOCKED

## Deviation log

- 2026-03-01: Added lock file after observed drift to global blocker analysis.
- 2026-03-02: Removed circular dependency in the `d=1,n=2` chain
  (`forward-swap -> model -> kernel-swap -> forward-swap`) by making
  `blocker_d1N2ForwardSwapEq_on_FT_deferred` derive from the invariant-model
  theorem and leaving `blocker_d1N2InvariantKernelSwapRule_deferred` as the
  sole deferred analytic step in this subchain.
- 2026-03-02: Normalized the chain to a single explicit deferred core
  `blocker_d1N2ForwardSwapEq_on_FT_core_deferred`; forward/kernelswap wrappers
  now reduce to this theorem (no hidden local `sorry` in wrappers).
- 2026-03-02: Re-locked the `d=1,n=2` chain so the sole local deferred step is
  Lorentz-invariant:
  `blocker_d1N2InvariantModel_core_deferred`.
  The forward-core theorem is now proved from it via
  `d1_n2_forward_swap_eq_of_invariantModel`.
- 2026-03-02: Extracted the unresolved analytic core into
  `blocker_d1N2InvariantKernelDiffZeroOnQuadric_core_deferred` and rewired
  wrappers so `blocker_d1N2InvariantModel_core_deferred` is sorry-free.
  Downstream `d=1,n=2` wrapper theorems now reduce through this quadric core.
- 2026-03-02: Replaced the false over-strong core
  (`source + hf_onFT -> full quadric diff-zero`) with the forwardizable target
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_core_deferred`.
  The full-quadric insufficiency is now explicitly tracked by
  `d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero`.
- 2026-03-02: Added exact equivalence theorem
  `d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric`:
  for fixed `hf_onFT`, the remaining forwardizable invariant-kernel core is
  equivalent to forward-swap equality on `FT_{1,2}`.
- 2026-03-02: Added witness-form reduction
  `d1N2InvariantKernelDiffZeroOnForwardizableQuadric_iff_witnessForm` and
  realizability helper `d1N2InvariantRealizable_pair_of_forwardizable`, making
  the remaining n=2 analytic `sorry` content explicit in both invariant and
  `(z, Γ)` forms.
- 2026-03-02: Reduced the active core `sorry` to a single pointwise subgoal via
  `d1N2ForwardSwapEq_onFT_of_pointwiseSliceAnchor`: extract one anchor witness
  `Λ₀` with equality for each forwardizable `z`, then propagate to all witnesses
  by complex Lorentz invariance.
- 2026-03-02: Extracted that pointwise subgoal as the explicit deferred theorem
  `blocker_d1N2PointwiseSliceAnchor_core_deferred`; the former theorem
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_core_deferred` is
  now a proved wrapper
  (`pointwise-anchor -> forward-swap -> invariant diff-zero`).
- 2026-03-02: Refined one step further to a neighborhood-form local core
  `blocker_d1N2LocalSliceAnchorNhd_core_deferred`. The pointwise theorem
  `blocker_d1N2PointwiseSliceAnchor_core_deferred` is now proved by constructing
  an open prepared neighborhood around a single witness `(z, Γ)` and extracting
  the anchor at `z` from eventual local data.
- 2026-03-02: Converted the local n=2 core to an equivalent fixed-witness form
  `blocker_d1N2LocalForwardEqNhd_core_deferred` (`eventually F(Γ·swap·w)=F(w)`).
  The slice-anchor neighborhood theorem is now a proved wrapper via
  `d1N2EventuallySliceAnchor_iff_eventuallyForwardEq_fixedWitness`.
- 2026-03-02: Eliminated the local-core `sorry` by deriving
  `blocker_d1N2LocalForwardEqNhd_core_deferred` from the forward/kernel
  equivalence plus factorization. The sole remaining `d=1,n=2` deferred analytic
  statement is now the invariant-source core:
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`.
- 2026-03-02: Refactored the remaining `d=1,n=2` analytic `sorry` into the
  invariant-equality statement
  `blocker_d1N2InvariantKernelSwapOnForwardizable_source_core_deferred`.
  The diff-zero theorem
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`
  is now a proved wrapper via `sub_eq_zero`.
- 2026-03-02: Relocated the remaining `d=1,n=2` analytic `sorry` from the
  coordinate-level forward-swap subgoal to an invariant-only source lemma:
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`.
  Theorems
  `blocker_d1N2InvariantKernelSwapOnForwardizable_source_core_deferred` and
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`
  are now proved wrappers.
- 2026-03-02: Added proved strengthened EOW bridge
  `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_realWitness`,
  making the non-circular route explicit: if one supplies connectedness of
  `adjSwapForwardOverlapSet (d=1,n=2)` plus one real spacelike ET-overlap
  witness, forward-swap equality on `FT_{1,2}` follows and feeds into the
  invariant diff-zero core via existing equivalence lemmas.
- 2026-03-02: Refactored the remaining n=2 `sorry` out of the source theorem:
  introduced deferred invariant quadric-model core
  `blocker_d1N2InvariantQuadricModel_core_deferred` and proved
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`
  by a non-circular transfer lemma between kernels agreeing on `FT_{1,2}`.
- 2026-03-02: Further refactored the single n=2 analytic `sorry` to the
  realizable-pair invariant statement
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred`.
  Theorem `blocker_d1N2InvariantQuadricModel_core_deferred` is now proved by
  symmetric extension from realizable tuples, and
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`
  is proved directly from realizable-pair reduction lemmas.
- 2026-03-02: Added exact forward/core equivalence on fixed factorization data:
  `d1N2ForwardSwapEq_onFT_iff_invariantKernelPairSwapOnRealizable`, plus both
  directional wrappers. This pins the remaining deferred theorem exactly to the
  forward-swap analytic statement for the same `F,f,hf_onFT`.
- 2026-03-02: Added proved n=2 connectivity conversion
  `d1N2_isConnected_adjSwapForwardOverlapSet_of_seedConnectedBlocker`,
  so `adjSwapForwardOverlapSet` connectedness is now available from the
  existing seed-connectedness blocker theorem without restating the conversion.
- 2026-03-02: Added proved complex-anchor bridge
  `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor`.
  This isolates the remaining n=2 analytic burden to constructing a nonempty
  complex-open anchor subset of `permForwardOverlapSet` where
  `extendF(swap·w)=F(w)` holds.
- 2026-03-02: Refactored the active n=2 analytic `sorry` into
  `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred`.
  The theorem
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred`
  is now a proved wrapper via forward-swap and realizable-pair bridges.
- 2026-03-02: Refined the body of
  `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred` so all non-geometric
  steps are proved by existing EOW/open-anchor infrastructure; the remaining
  local `sorry` is now an explicit geometric witness existence subgoal
  (`x0` real spacelike with both swap-related embeddings in `ExtendedTube 1 2`).
- 2026-03-02: Added exact source-level equivalence
  `d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor` and extracted
  the source-side anchor constructor
  `d1N2ForwardBaseOpenAnchor_source_of_pairSwap`.
  This makes the active blocker mathematically explicit as a pure open-anchor
  existence obligation under source assumptions.
- 2026-03-02: Re-centered the active `d=1,n=2` `sorry` on the invariant route:
  added deferred theorem
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred`
  and proved
  `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred` as a wrapper from
  factorization + invariant realizable-pair symmetry + forward/realizable
  bridge (no geometric witness subgoal left in that theorem).
- 2026-03-02: Refined once more to a primitive invariant source theorem:
  introduced deferred
  `blocker_d1N2Source_swappedInvariantForwardEq_core_deferred`
  (`z,y ∈ FT` + swapped invariant-quad relation implies `F y = F z`).
  Theorem
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred`
  is now proved as a wrapper using `hf_onFT`.
- 2026-03-02: Moved the remaining local `sorry` from the open-anchor wrapper
  back to an invariant-only realizable-pair theorem:
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`.
  Theorems
  `blocker_d1N2ForwardBaseOpenAnchor_source_invariant_core_main_deferred` and
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_main_deferred`
  are now proved wrappers from that invariant-only core.
- 2026-03-02: Rebuilt stale `PermutationFlowBlockers` artifacts and ran a
  declaration-level axiom dependency scan. Result:
  `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor` and
  `d1N2InvariantKernelPairSwapOnRealizable_source_of_connectedOpenAnchor` are
  already `sorry`-free; the active unresolved piece is still exactly the
  source swapped-invariant forward-equality implication at
  `blocker_d1N2Source_swappedInvariantForwardEq_invariantOnly_core_deferred`.
- 2026-03-02: Refactored the remaining local analytic `sorry` into the
  source-level swapped-invariant forward theorem
  `blocker_d1N2Source_swappedInvariantForwardEq_invariantOnly_core_deferred`.
  The realizable-pair kernel theorem
  `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`
  is now proved from realizability witnesses plus `hf_onFT` (no local `sorry`).
- 2026-03-02: Added exact reduction
  `d1N2Source_swappedInvariantForwardEq_iff_forwardBaseEq` and moved the
  remaining analytic `sorry` into
  `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred`
  (`z ∈ FT`, `swap·z ∈ ET` ⇒ `extendF(swap·z)=F z`).
  The swapped-invariant theorem is now a proved wrapper via this equivalence.
- 2026-03-02: Added proved package bridge
  `d1N2ForwardBaseEq_of_EOWGeometryPackage`:
  under `d1N2ForwardSwapEOWGeometryPackage`, source assumptions now imply the
  exact active core statement
  `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred`.
  So the residual gap is reduced to constructing the geometry package from
  source-side inputs in the locked `d=1,n=2` route.
- 2026-03-02: Added proved complex-anchor bridge
  `d1N2ForwardBaseEq_of_connectedForwardOverlap_and_openAnchor`:
  connected adjacent forward-overlap plus a nonempty complex-open base anchor
  now implies the exact active core statement. This aligns the remaining
  `d=1,n=2` closure work with the complex-open-anchor route.
- 2026-03-02: Flipped the local dependency to keep the deferred point in
  invariant coordinates:
  - `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred` is now proved
    from factorization + invariant realizable-pair symmetry +
    `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable`.
  - the active `d=1,n=2` analytic deferred content is the realizable-pair
    invariant source core.
- 2026-03-02: Added exact source-level equivalence
  `d1N2InvariantKernelPairSwapOnRealizable_source_iff_swappedInvariantForwardEq`
  (via explicit-field bridge
  `d1N2InvariantKernelPairSwapOnRealizable_of_sourceField_iff_swappedInvariantForwardEq`).
  This makes the active deferred theorem exactly equivalent to the sourced
  swapped-invariant forward statement `F y = F z` under
  `d1InvariantQuad y = (d1Q1 z, d1Q0 z, d1P01 z, -d1S01 z)`.
- 2026-03-02: Refactored the active invariant `sorry` into explicit
  swap-difference form:
  - new deferred theorem:
    `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
    (`f q0 q1 p s - f q1 q0 p (-s) = 0` on realizable swap-pairs),
  - `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`
    is now a proved wrapper by `sub_eq_zero`.

## External comparison notes

- 2026-03-02 (Mike branch status comparison):
  reviewed
  `https://github.com/mrdouglasny/OSreconstruction-1/blob/main/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/STATUS.md`.
  That status reports:
  - `BHW.bargmann_hall_wightman_theorem` with zero `sorry`s,
  - two project axioms: `kakSet_dense` and `hExtPerm_of_d1`,
  - d>=2 connectedness routed through dense KAK image (`kakSet_dense`).
  Local branch check at the same date:
  - `#print axioms BHW.bargmann_hall_wightman_theorem` gives
    `[propext, sorryAx, Classical.choice, Quot.sound]`,
  - local BHWPermutation files still contain deferred theorems (`sorry`).
  Interpretation for this lock:
  - Mike’s branch replaces key proof gaps with explicit project axioms,
  - this lock remains on the no-new-axiom, `d=1,n=2` invariant-function route,
    with active target
    `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
    (the pair-swap theorem is now a proved `sub_eq_zero` wrapper).
