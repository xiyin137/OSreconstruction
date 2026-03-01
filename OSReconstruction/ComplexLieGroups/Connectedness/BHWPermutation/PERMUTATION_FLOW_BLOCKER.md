# PermutationFlow Sorry Blocker (2026-02-28)

This note documents the remaining blocker in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`.

## Status Update (2026-03-01, current canonical view)

Current active deferred declarations in `PermutationFlow.lean` are:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_d1_leftAdjSwap_scheme_inputs`

The third item is now the only non-connectivity blocker in the active route.
Its `n ≤ 1` branch is now fully discharged (vacuous adjacent-index quantifiers),
so only the genuine `n ≥ 2` geometry remains.

Its precise obligations are:

- `hSwap`: adjacent-swap ET-overlap invariance for `extendF` in `d=1`,
- `hAnchor`: nonempty step-anchor set
  `{z | z ∈ D_(swap*σ) ∧ swap·z ∈ ET}` for each step.

Current code progress inside `hAnchor`:

- `σ = 1` branch: proved.
- `σ = swap(i,i+1)` branch: proved (via direct adjacent sector-overlap witness).
- `n = 2` is eliminated in the remaining branch by explicit permutation
  classification (`Perm(Fin 2)` has only `1` and `swap`).
- remaining branch: `n ≥ 3`, `σ ≠ 1`, and `σ ≠ swap(i,i+1)`.

Recent formal checks relevant to this blocker:

- `test/witness_test.lean` is fully checked and provides a concrete
  `d=1, n=2` positive witness (`w ∈ FT` with `swap·w ∈ ET`).
  This helps with local nonemptiness sanity but does not close global `hAnchor`.

- `test/proofideas_ih_composition.lean` now has no `sorry` and includes a
  complete formal `route_B_counterexample_statement` (`swap⁻¹·FT ⊄ ET` in
  `d=1`) alongside the IH-composition infrastructure.

- midpoint implication routes are already formally refuted in test files
  (`midpoint_route_vacuous_test.lean`, `midpoint_condition_d1_counterexample_test.lean`),
  so they should be treated as closed-negative branches.

Important current negative result for closure planning:

- the existing adjacent-swap wrapper in `Adjacency.lean` that proves ET-overlap
  invariance from connectedness still needs a real spacelike overlap witness,
  and there is no general `d=1` witness package in production code.
  So `hSwap` is not yet obtainable from that route alone.

- heuristic numerical checks (non-formal) suggest this global anchor condition
  may fail for some `d=1, n=3` permutations, so it should be treated as
  potentially too strong until geometrically validated.

These are now documented in:

- `D1_SCHEME_INPUTS_NOTES.md` (same folder).

This replaces older local-gluing/back-witness wording as the canonical blocker
description for current code.

Historical status entries follow below for audit trail; they are not the current
blocker definition.

## Location

Current deferred declarations in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`

## Status Update (2026-03-01, blocker-shape correction)

Current `PermutationFlow.lean` warnings are exactly:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_zero_nhds_d1_holo`

The temporary third blocker
`deferred_eventually_backWitness_nhds_d1` was removed from the active route.
Reason: that statement asks for local eventual existence of exact
back-witnesses `Λ·(σ·w)=w`, which is too strong and nongeneric in `d=1`.

Concrete failure pattern (already aligned with existing d=1 rigidity theorems):

- `d=1, n=2, σ=swap`, choose `Γ = -Id` (rapidity `i*pi`), so `Γ·(σ·w) ∈ FT`
  can hold on a prepared neighborhood.
- Generic swap back-witness does not exist (`u1 ≠ ±u0` / `v1 ≠ ±v0` cases in
  `D1OrbitSet.lean`).

So the singular non-connectivity blocker is again correctly stated as the local
holomorphic gluing theorem `deferred_eventually_zero_nhds_d1_holo`.

## Status Update (2026-03-01, scheme-route rewiring)

`PermutationFlow.lean` has now rewired the `d=1` ET-overlap bridge to the
left-adjacent induction scheme and removed the old local-gluing chain from the
active path.

Current three deferred declarations are:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_d1_leftAdjSwap_scheme_inputs`

So the singular non-connectivity blocker is no longer
`deferred_eventually_zero_nhds_d1_holo`; it is now the geometric package
`deferred_d1_leftAdjSwap_scheme_inputs`, which asks for:

- adjacent-swap ET-overlap `extendF` invariance family, and
- triple ET-membership witnesses for each left-adjacent induction step.

This matches the IH-composition architecture directly and avoids the previous
prepared-neighborhood analytic detour.

## Status Update (2026-03-01, IH-composition proofideas refresh)

`test/proofideas_ih_composition.lean` now compiles with exactly one intentional
`sorry`:

1. `route_B_counterexample_statement`

The previous witness-level `sorry` for `overlap_witness_swap_in_ET` was removed
by switching to the existing certified witness source
`adjSwapForwardOverlap_nonempty (d := 1)`.

So the proofideas file now provides fully checked infrastructure for:

- lifting FT-level IH to ET-overlap `extendF`-invariance,
- composing IH + adjacent-swap invariance on triple-overlap intersections,
- openness of the triple-overlap domain.

Mainline integration caveat remains unchanged:

- the d=1 branch still needs a production route supplying adjacent-swap
  `extendF` invariance plus nonempty step anchors in the exact form consumed by
  `PermutationFlow.lean` induction plumbing.
- `PermutationFlow.lean` now contains
  `extendF_perm_overlap_of_leftAdjSwap_scheme`, a reusable induction skeleton
  that closes ET-overlap permutation invariance once those three geometric
  inputs are instantiated.
- New helper reductions were added in `PermutationFlow.lean`:
  - `leftAdj_anchor_nonempty_of_ET_triple`
  - `ET_triple_nonempty_of_leftAdj_anchor`
  - `leftAdj_anchor_nonempty_base`
  - `extendF_perm_overlap_d1_of_leftAdjSwap_scheme_inputs`

These isolate the step-anchor problem to a clean triple-membership target:

- produce `y` with `y ∈ ET`, `swap·y ∈ ET`, and `σ·y ∈ ET`,
- then left-step anchor nonemptiness follows formally.
- conversely, any left-step anchor gives such a triple witness (equivalence by
  `y = swap·z`), so either formulation can be used as the deferred geometric input.
- together with adjacent-swap ET-overlap invariance, this now closes the whole
  d=1 ET-overlap permutation statement by a single scheme theorem call.

## Status Update (2026-02-28, axiom-free rollback)

`PermutationFlow.lean` has no `axiom` placeholders.
Current Lean warnings in that file are:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_exists_open_backWitness_nhds_d1`

The d=1 local zero-neighborhood theorem
`deferred_exists_open_zero_nhds_d1_holo` now runs through the back-witness
route (`_hBackRoute`).

## Status Update (2026-03-01, current blocker reality)

Current active `sorry` declarations in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_backWitness_nhds_d1`

The third item is still the singular non-connectivity blocker.

### Why this remains blocked

The prepared-domain assumptions in
`deferred_eventually_zero_nhds_d1_holo` give:

- `w ∈ FT`,
- `σ·w ∈ ET`,
- `Γ·(σ·w) ∈ FT`,

but do **not** give a local back-witness `Λw` with `Λw·(σ·w)=w`.

Without such identification (or an equivalent local overlap-uniqueness input),
the identity
`F(Γ·(σ·w)) = F(w)` is not derivable from existing invariance lemmas.

Refactor status:

- `deferred_eventually_zero_nhds_d1_holo` is now proved by reducing to
  `eventually_zero_nhds_of_eventually_back_witness_d1`.
- This isolates all remaining d=1 local gluing difficulty into
  `deferred_eventually_backWitness_nhds_d1`.
- The new third blocker is now stated in geometric form only (independent of
  `F`, boundary-value, and locality hypotheses), so analytic plumbing is fully
  out of the blocker.

### Formal obstruction now available in production code

`D1OrbitSet.lean` contains explicit `d=1, n=2` rigidity theorems:

- `swap_backWitness_n2_sum_rigidity`
- `swap_backWitness_n2_diff_rigidity`
- `not_exists_swap_backWitness_n2_of_sum_generic`
- `not_exists_swap_backWitness_n2_of_diff_generic`

These show local back-witness existence is nongeneric even in the smallest
swap case, so the back-witness route cannot be assumed as a generic local
gluing mechanism.

Also, in `PermutationFlow.lean` the midpoint orientation is explicitly
obstructed for the branch `π * swap(i,i+1) = σ`:

- `not_exists_open_midCondAtPermStep_nhds_of_mul_swap_eq_sigma_d1`.

So repeated midpoint retries are structurally misaligned with the d=1 geometry.

## Status Update (2026-02-28, local-gluing correction)

Current active `sorry` declarations in `PermutationFlow.lean` are:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_zero_nhds_d1_holo`

The third item replaced the previous back-witness placeholder as the explicit
local d=1 gluing gap.

### Why the new third theorem is likely too strong as currently stated

`deferred_eventually_zero_nhds_d1_holo` asks for eventual local vanishing of

- `g(w) = F(Γ·(σ·w)) - F(w)`

on a prepared neighborhood `U`, from:

- holomorphicity/invariance/locality assumptions on `F`,
- preparedness (`w ∈ FT`, `σ·w ∈ ET`, `Γ·(σ·w) ∈ FT` on `U`),
- connectedness of `permOrbitSeedSet`.

But these hypotheses do not provide a local mechanism identifying `w` with
`σ·w` in the same FT-evaluable orbit (for example, a local family
`Λw·(σ·w)=w`, or an equivalent overlap-domain uniqueness anchor).

So the theorem currently encodes a nontrivial geometric input, not a pure
analytic corollary. This is now the precise non-connectivity blocker.

## What is already proved and usable

### Local witness and transport machinery

- `JostWitnessGeneralSigma.jostWitness_exists` (for `d >= 2`) gives:
  - `exists x in JostSet`, with
  - `realEmbed x in ET` and `realEmbed (x ∘ sigma) in ET`.

- `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`
  reduces `hExtPerm` to connectedness of `permForwardOverlapSet`.

### Connectivity reduction chain (already in file)

- `isConnected_permForwardOverlapSet_of_indexConnected`
- `isConnected_permForwardOverlapIndexSet_of_seedConnected_and_seedOrbitPreconnected`
- `isConnected_permForwardOverlapIndexSet_d1_of_seedConnected`
- `isConnected_permOrbitSeedSet_iff_permForwardOverlapSet`

### New packaging helpers (already in file)

- `extendF_perm_overlap_of_jostWitness_and_seedConnected`
- `extendF_perm_overlap_dge2_of_seedConnected`
- `isConnected_permForwardOverlapSet_d1_of_seedConnected_and_nonempty`

These keep the final branch modular, but they still require the same missing geometric inputs.

### New open-anchor infrastructure (new production module)

- `Connectedness/BHWPermutation/OverlapAnchor.lean` now provides:
  - `extendF_perm_overlap_of_forward_base`
  - `forward_base_eq_of_open_anchor`
  - `extendF_perm_overlap_of_forward_open_anchor`
  - `extendF_perm_overlap_of_overlap_real_open_anchor`
  - `exists_overlap_open_anchor_of_eventuallyEq_local`
  - `extendF_perm_overlap_of_eventuallyEq_anchor_and_forwardOverlapConnected`

This gives a second rigorous route:

- connectedness of `permForwardOverlapSet` + open anchor equality on a nonempty open subset
  -> base equality on all forward overlap
  -> full ET-overlap equality (`hExtPerm`).

It also now gives a third operational variant:

- local eventual equality at a single complex anchor in `D_σ`
  -> explicit open anchor in `D_σ`
  -> global ET-overlap equality (assuming connected forward overlap).

It does **not** remove the core connectedness blocker, but it decouples
"anchor propagation" from "global overlap geometry" for future d=1 and d>=2 attacks.

### Current compile status update

- `OverlapAnchor.lean` now compiles (the real-anchor identity theorem call was
  fixed by rewriting `f = g` as `(f - g) = 0` before applying
  `identity_theorem_totally_real_product`).
- `BHWPermutation.lean` compiles with this import.
- Active `sorry` set is exactly:
  1. `deferred_isConnected_permOrbitSeedSet_dge2`
  2. `deferred_isConnected_permOrbitSeedSet_d1`
  3. `deferred_exists_open_backWitness_nhds_d1`

d=1 reduction status:

- The d=1 bridge theorem `deferred_extendF_perm_overlap_d1_of_seedConnected`
  is now fully proved from:
  - seed connectedness -> forward-overlap connectedness (already wired),
  - one explicit forward-base theorem
    `deferred_forward_base_perm_eq_d1_of_seedConnected`,
  - then automatic lift to full ET-overlap equality via local
    `PermutationFlow` transport lemmas.
- The forward-base theorem is now proved by open-anchor propagation
  (`forward_base_eq_of_open_anchor_local`).
- The d=1 local zero theorem `deferred_exists_open_zero_nhds_d1_holo` is now
  wired through the back-witness route (`_hBackRoute`).
  The remaining d=1 local geometric blocker in this pipeline is
  `deferred_exists_open_backWitness_nhds_d1`.
  The older midpoint-closure target was removed from the active route because
  the branch `π * swap_i = σ` is geometrically obstructed in `d=1`.
  The obstruction branch `π * swap_i = σ` is now explicitly formalized by
  `mem_closure_midCondBadAtPermStep_of_mul_swap_eq_sigma_d1`, showing anchor
  badness/closure in that orientation, and by
  `not_exists_open_midCondAtPermStep_nhds_of_mul_swap_eq_sigma_d1`, showing
  that no local midpoint-implication neighborhood can exist there.
  The intermediate preparation step is now proved as
  `exists_open_nhds_overlap_and_forward_of_anchor_d1`.
  The prepared-domain theorem
  `deferred_exists_open_eq_nhds_d1_on_prepared_domain` is now assembly only.
  The eventual-form theorem
  `deferred_local_eventually_Feq_d1_at_anchor` is now proved from this by a
  standard open-neighborhood-to-eventual conversion.
  The existence part of the anchor package is now separated and proved as
  `exists_forward_anchor_with_lorentz_of_seedConnected_d1`, and the full wrapper
  `deferred_forward_eventually_Feq_d1_of_seedConnected_nontrivial` is now assembly.
  The resulting eventual `F`-equality is converted to an explicit open anchor via
  `eventually_extendF_base_eq_of_eventually_forward_eq_fixedLorentz`
  and `exists_forward_open_anchor_of_eventuallyEq_local`.

Latest obstruction detail (current turn):

- We tested a direct orbit-transport closure of the local zero equation using
  `g(w) = F(Γ·(σ·w)) - F(w)`.
- The route would close if, for each prepared `w`, there were a Lorentz witness
  `Λw` with `Λw·(σ·w) = w`; then both terms are identified via FT-side complex
  Lorentz invariance.
- Current hypotheses provide only that `σ·w` can be sent to *some* FT point, not
  specifically to `w`, so the argument cannot be completed.

New production fact now available (from `Adjacency.lean`):

- `adjSwap_not_mem_forwardTube_d1`:
  for any adjacent swap index in `d=1`,
  `z ∈ FT -> swap(z) ∉ FT`.

This formalizes the core obstruction used in the midpoint-orientation diagnosis.

### Structural obstruction in the midpoint route (`d = 1`)

There is a concrete configuration where the current fixed-step midpoint
implication schema is incompatible with the prepared-domain hypotheses.

Fix any adjacent index `i` and set
`ip1 := ⟨i.val + 1, hi⟩`, `swap := Equiv.swap i ip1`, and
`π := σ * swap`.

Then:

1. `π * swap = σ` (because `swap * swap = 1`).
2. On a prepared domain `U`, we assume
   `complexLorentzAction Γ (permAct σ w) ∈ FT` for all `w ∈ U`.
   Therefore the midpoint antecedent
   `A(w) := Γ·((π*swap)·w) ∈ FT` is true for all `w ∈ U`.
3. The midpoint consequent is
   `B(w) := Γ·(π·w) ∈ FT = Γ·((σ*swap)·w) ∈ FT`.
   Using Lorentz/permute commutation, this is
   `swap(Γ·(σ·w)) ∈ FT`.
4. In `d = 1`, adjacent swap does not preserve forward-tube membership:
   for any `z ∈ FT`, `swap(z) ∉ FT` (the forward-time inequalities reverse at
   the swapped adjacent step).

Hence, from preparedness we get `A(w)` true but `B(w)` false on `U` for this
choice `π = σ*swap`. So the implication `A -> B` cannot hold on any neighborhood,
and the fixed-step closure-separation target
`w0 ∉ closure (U ∩ midCondBadAtPermStepSet_d1 ...)` is generally false in that
branch.

Consequence:

- the remaining third sorry is not just "hard"; it indicates the midpoint-chain
  orientation itself is unsuitable for the `d = 1` geometry.
- the d=1 route should pivot to a direct overlap-domain analytic continuation
  argument (boundary/anchor on `D_σ`) rather than this FT-midpoint implication
  transport.

## Why this blocker is hard

All currently sound routes collapse to one of two missing global ingredients:

1. `IsConnected (permOrbitSeedSet n sigma)`
2. A d=1-specific local midpoint-stability / complex-anchor geometric input

### Key negative facts (already established in tests)

- No real ET pair/Jost witness for `d=1`, `n=2`, adjacent swap:
  - `test/d1_no_real_witness_swap_n2_probe.lean`
    - `no_real_et_pair_swap_n2`
    - `no_real_jost_witness_swap_n2`

- Midpoint-drop implication is false in `d=1`:
  - `test/midpoint_condition_d1_counterexample_test.lean`
- Additional numerical probe (`d=1`, `n=2`, swap) found prepared points with
  `w ∈ FT` and `Γ·(swap·w) ∈ FT` but `Γ·w ∉ FT`, confirming local midpoint-bad
  points can occur inside prepared domains.

- Some naive global-topology shortcuts are invalid:
  - `test/nonempty_domain_d1_counterexample.lean`
  - `test/nonempty_domain_complement_not_open_d1.lean`

So the stale proof attempts fail for structural reasons, not syntax gaps.

## Current minimal blocker decomposition

To close the `sorry` without adding assumptions, one of the following must be completed:

### Route A (d >= 2 + d=1 split)

- Prove seed/forward-overlap connectedness in `d >= 2`:
  - enough to feed `extendF_perm_overlap_dge2_of_seedConnected`
- Build a new d=1 complex-anchor mechanism (not real Jost-point based)

### Route B (uniform all d >= 1)

- Prove connectedness of `permForwardOverlapSet` directly for all `d >= 1`
- Apply `extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected`
  where witness exists, plus d=1 alternative witness mechanism

### Route C (new iterative extension infrastructure)

- Generalize adjacent EOW extension step to sector data
  (`PermExtensionData` step for `swap * sigma`) and avoid `hExtPerm`
  reduction entirely.

This is conceptually clean but requires substantial new domain-gluing machinery.

### Route D (open-anchor route, now formalized)

- Prove `IsConnected (permForwardOverlapSet n sigma)`
- Construct a nonempty open `W ⊆ permForwardOverlapSet` where
  `extendF F (sigma·w) = F w`
- Apply `extendF_perm_overlap_of_forward_open_anchor`

Important caveat for d = 1:

- `forward_base_eq_of_real_open_anchor` is formally correct, but for `n > 0`
  it is not directly usable on `permForwardOverlapSet` because that set is inside
  `ForwardTube`, and `ForwardTube` has no real points.
- Replacing the anchor by a mere accumulation-point condition is not enough on
  these multivariable domains: SCV identity requires a stronger uniqueness
  anchor (complex-open, or totally-real-open with dedicated theorem).
- So the remaining d = 1 work is specifically a **complex-anchor/gluing**
  problem (or an equivalent non-real-anchor propagation theorem), not a
  connectedness plumbing issue.

## Recommended next attack (most pragmatic)

1. **Prove a d>=2 theorem in `BHWPermutation`**:
   - `isConnected_permOrbitSeedSet_dge2` (or equivalent forward-overlap form)
2. Wire that into the existing helper:
   - `extendF_perm_overlap_dge2_of_seedConnected`
3. For d=1, introduce a dedicated complex-anchor theorem on
   `permExtendedOverlapSet` (no real-anchor assumptions).

This keeps the existing architecture and only fills the genuine geometric gap.

## Precise replacement target for the d=1 local blocker

Given the proved obstruction in the branch `π * swap(i,i+1) = σ`, the current
fixed-step closure theorem
`deferred_not_mem_closure_midCondBadAtPermStep_d1` should be treated as an
over-strong target.

A mathematically consistent local theorem to aim for is:

```lean
private theorem deferred_exists_open_backWitness_nhds_d1
  ... :
  ∃ W, IsOpen W ∧ w0 ∈ W ∧ W ⊆ U ∧
    (∀ w ∈ W, ∃ Λ : ComplexLorentzGroup 1,
      complexLorentzAction Λ (permAct (d := 1) σ w) = w)
```

This aligns with already-proved infrastructure:

- `g_zero_on_prepared_of_back_witness_d1`
- internal `_hBackRoute` in `deferred_exists_open_zero_nhds_d1_holo`

So the d=1 local gluing reduction can remain structurally the same while
switching from midpoint-step closure separation to a back-witness neighborhood
construction.

## Useful files

- Main blocker:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`
- d>=2 Jost witness package:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/JostWitnessGeneralSigma.lean`
- Adjacent overlap infrastructure:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`
- d=1 orbit/slice tools:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/IndexSetD1.lean`
  - `OSReconstruction/ComplexLieGroups/D1OrbitSet.lean`
- Probe notes/tests:
  - `test/iterated_eow_perm_ext_test.lean`
  - `test/proofideas_iterated_eow_perm_ext.lean`
  - `test/seed_connectedness_probe.lean`

## Quick check command

```bash
lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean
```

Expected currently: three warnings for declarations using `sorry`.

## Status Update (2026-03-01, non-vacuity check)

The local d=1 blocker hypotheses are genuinely satisfiable in nontrivial
cases (checked numerically for `n=2`, `σ=swap`): there exist `w ∈ FT` and a
fixed complex Lorentz witness `Γ` with `Γ·(σ·w) ∈ FT`.

Therefore `deferred_eventually_zero_nhds_d1_holo` is not eliminable by showing
its assumptions are contradictory; it requires a real local gluing argument.

## Next candidate proof shape

Recast the blocker as a two-tube local gluing problem:

- `f1(w)=F(w)` on `T1=FT`,
- `f2(w)=F(Γ·(σ·w))` on `T2={w | Γ·(σ·w) ∈ FT}`,
- prove local agreement on `T1 ∩ T2` near the prepared anchor.

This appears closer to a direct EOW-style local theorem than the failed
midpoint/back-witness routes.

## Status Update (2026-03-01, blocker normalization)

Refactor complete in `PermutationFlow.lean`:

- `deferred_eventually_zero_nhds_d1_holo` is now a proved wrapper.
- The single local d=1 blocker is normalized to
  `deferred_eventually_forward_eq_nhds_d1_holo`.

So the active deferred set is now:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_forward_eq_nhds_d1_holo`

This is the same mathematical gap as before, stated in its core form:
local eventual equality of `F(Γ·(σ·w))` and `F(w)` on a prepared neighborhood.

## Status Update (2026-03-01, stronger decomposition)

Further reduction landed in `PermutationFlow.lean`:

- `deferred_eventually_forward_eq_nhds_d1_holo` is now **proved**.
- It is proved by:
  1. shrinking to a connected complex ball `D = ball(w0, ε) ⊆ U`,
  2. applying `identity_theorem_totally_real_product` to
     `h(w)=F(Γ·(σ·w)) - F(w)` on `D`,
  3. using a real-open anchor set `V` where `h=0`.

The only remaining local d=1 blocker is now the anchor-extraction theorem:

- `deferred_exists_real_open_anchor_eq_d1_on_ball`.

So active deferred declarations are exactly:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_exists_real_open_anchor_eq_d1_on_ball`

This is a cleaner blocker shape than before: pure local real-anchor extraction,
with all analytic propagation already done.

## Erratum (2026-03-01, authoritative current state)

Some older sections above describe intermediate branches that were later
rolled back. The authoritative compile state is:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_forward_eq_nhds_d1_holo`

The real-open-anchor-on-ball branch is not the active code path.

## Next technical route under investigation: `Lambda`-slice continuation

For fixed prepared `(w, Γ)`, define

- `H(Λ, w) := F(complexLorentzAction Λ (permAct σ w)) - F w`,
- local slice `S_w := {Λ | complexLorentzAction Λ (permAct σ w) ∈ FT}`.

Facts already available:

- `S_w` is nonempty whenever `w ∈ permForwardOverlapSet`,
- in `d=1`, fixed-`w` slices are connected (`IndexSetD1` machinery).

Missing ingredient:

- a rigorous local anchor on the slice forcing `H(Λ, w)=0` at one `Λ ∈ S_w`
  for `w` near `w0`, and then propagation in `Λ`.

This route avoids the obstructed midpoint orientation, but still needs a
nontrivial anchor mechanism (not currently available from existing hypotheses).

## Status Update (2026-03-01, slice route wired in code)

The `Lambda`-slice route is now partially formalized in
`PermutationFlow.lean`:

1. `forward_eq_of_slice_anchor_d1`
2. `eventually_forward_eq_nhds_of_eventually_slice_anchor_d1`

And the blocker theorem `deferred_eventually_forward_eq_nhds_d1_holo` is now a
wrapper reducing to one missing input:

- eventual local existence of a slice anchor `Λ₀` with
  `Λ₀·(σ·w) ∈ FT` and `F(Λ₀·(σ·w)) = F(w)`.

So the third sorry is no longer an opaque full gluing claim; it is an explicit
local anchor-existence gap in the slice formulation.

## Cross-check: `test/proofideas_ih_composition.lean` (2026-03-01, updated)

Current Lean status for that file: **1 sorry only** (`route_B_counterexample_statement`).

Previous witness-level sorrys (`overlap_witness_in_FT`, `overlap_witness_swap_in_ET`)
were eliminated by switching to the existing certified source
`adjSwapForwardOverlap_nonempty (d := 1)`.

Additionally, `test/witness_test.lean` now provides a fully compiled constructive
proof of the d=1,n=2 overlap, with:
- explicit witness `w = ((i,-2),(2i,0))` proved in FT,
- explicit Lorentz boost `Λ = [[3/5,-4i/5],[-4i/5,3/5]]` (Pythagorean triple)
  proved in SO+(1,1;C) (metric_preserving + det=1),
- `Λ·(swap·w) ∈ FT` verified by direct computation,
- `swap·w ∈ ET` concluded via `complexLorentzAction_inv`.

Everything in both test files typechecks (zero errors).

Important validation from this cross-check:

- The IH-lift pattern is sound in code:
  `F`-level permutation invariance on `FT` can be lifted to
  `extendF`-invariance on `ET ∩ σ⁻¹ ET`.
- This is already available in mainline as
  `extendF_perm_overlap_from_forwardTube_permInvariance` in `PermutationFlow.lean`.

Order convention note (critical for composition steps):

- With the current `permAct` convention, one has
  `permAct (π * τ) z = permAct τ (permAct π z)`.
- Any composition lemma using `(swap * σ)` must respect this order; otherwise
  one gets an incorrect midpoint equation and Lean goal mismatch.

Implementation note landed in `PermutationFlow.lean`:

- Added `extendF_perm_eq_leftMul_adjSwap_of_forwardIH_and_anchor`.
- This packages exactly the IH-composition route:
  1. lift FT-level IH to ET-overlap via
     `extendF_perm_overlap_from_forwardTube_permInvariance`,
  2. compose with adjacent-swap `extendF`-invariance on the anchor set,
  3. propagate to all of `D_(swap*σ)` by connected open-anchor identity theorem.

So the remaining gap is explicitly geometric (connectedness + anchor existence),
not analytic-gluing architecture.
