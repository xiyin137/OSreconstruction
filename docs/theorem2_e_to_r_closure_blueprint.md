# Theorem 2 and E-to-R Closure Blueprint

Status: live closure control plane, created after checkpoint `f963089e`.

Purpose: keep the remaining Theorem 2 and E-to-R work readable.  The giant
`docs/theorem2_locality_blueprint.md` remains the archive and detailed
transcript store.  This file is the short operational plan.  If this file
starts becoming an archive, split detailed proof transcripts into focused
companion notes and keep this file as the index.

## Route Locks

The active route is strict OS-II through the OS-I section 4.5 Figure 2-4
locality argument.

Do not use source-variety descent, normalized Riemann-style extension, quotient
descent, global monodromy packaging, final theorem wrappers around unproved
inputs, or downstream deterministic adjacent branches as upstream data.

Do not introduce new trust boundaries or placeholder proofs.  The only accepted
neutral trust boundary on this local chain remains
`BHW.localSPrime_twoSectorBranch_of_EOW_BHW`.

Use targeted checks only:

```text
lake env lean <exact-file>
lake build <exact-frontier-module>
git diff --check -- <touched-files>
```

The active adjacent initial germ is the genuine OS-I `(4.12)` germ:

```text
Omega0 =
  { z | BHW.permAct P.tau z in BHW.ForwardTube d n } inter H.OmegaJ

B0 z =
  bvt_F OS lgc n (BHW.permAct P.tau z)

p0 = gamma 0
```

This is not the later deterministic branch `extendF` composed with the
permutation action.  Endpoint traces stay endpoint-centered: Wick traces use
`t = 0`, horizontal common-edge traces use `t = 1`, and arbitrary chart traces
are transported only after overlap equality has been proved.

## Current Checked State

Recent checkpoint:

```text
f963089e Prove OS45 pre-Hdiff flat pairing equality
```

Checked local support now includes:

| Item | Status |
| --- | --- |
| Metric-ball product identity helpers | Checked in `OSReconstruction/SCV/OverlapIdentity.lean`. |
| Pure side-continuity helper | Checked in `OSReconstruction/SCV/LocalEOWSideContinuity.lean`. |
| OS45 local EOW, source-to-flat, and branch transport reducers | Checked in `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45BHWJostLocal.lean`. |
| Pre-`Hdiff` flat source-pairing equality | Checked as `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick`. |
| Signed side source-test pointwise formula | Checked as `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_apply`. |
| Signed side source-test common Schwinger limit | Checked as `BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`. |
| Local source-window side-test support | Checked as `BHW.os45FlatCommonChart_sideSupport_radius_sourceImage` and `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_tsupport_subset_image_eventually`. |
| Pointwise source common-edge to flat zero-height bridge | Checked as `BHW.os45FlatCommonChart_zeroHeight_pairings_eq_of_sourceCommonEdge_eqOn`. |
| Pointwise source common-edge to ambient flat EOW seed | Checked as `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`. |
| Initial and endpoint metric-ball continuation charts | Checked as `BHW.OS45BHWJostHullData.ordinaryWick_metricBallChartInWindow`, `BHW.OS45BHWJostHullData.OS412SeedWindow_metricBallChartInWindow`, `BHW.OS45BHWJostHullData.ordinaryCommonEdge_metricBallChartInWindow`, `BHW.OS45BHWJostHullData.adjacentCommonEdge_metricBallChartInWindow`, and `BHW.OS45BHWJostHullData.commonEdgeDifference_metricBallChartInWindow`. |
| All-overlap metric-ball identity propagation | Checked as `SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds`. |
| Common side-limit zero-height equality | Checked as `SCV.eq_zeroHeight_of_common_sideLimit`. |
| Authorized local SPrime two-sector continuation input | Available as `BHW.localSPrime_twoSectorBranch_of_EOW_BHW`. |

The pre-`Hdiff` source equality is important because it gives the flat `(4.14)`
source anchor before `Hdiff`, common-boundary CLM, or local SPrime branch
exists.  It proves equality of the ordinary `(4.1)` and genuine adjacent
`(4.12)` source pairings against the same cutoff-pulled source test.  It is
not an EOW seed until the two analytic-element side traces have been
transported to the source-side limits.

## Live Mathematical Blocker

The next real target remains:

```lean
BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45
```

This theorem must directly construct the local Figure 2-4 `Hdiff` germ and its
local horizontal zero representation.  It is not a wrapper around later
reducers.

The live hard subgap is the adjacent all-overlap `Wadj` branch-law seed.  The
ordinary side `Word` and adjacent side `Wadj` must be produced while the
proof-local finite-chain data is still in scope.  They must be genuine ambient
complex-open overlap seeds, with metric-ball witnesses suitable for the checked
SCV identity helpers.

The direct proof must supply:

| Subtask | Required content |
| --- | --- |
| Ordinary analytic element | OS-I `(4.1)` local branch and Wick normalization. |
| Adjacent analytic element | Corrected OS-I `(4.12)` local branch from the genuine adjacent initial germ. |
| Local transfer along gamma | Case split into ordinary-sector, adjacent-sector, and flat real-Jost EOW transition. |
| Flat transition | Now has a checked non-circular consumer: once local `h45_source_eqOn` is proved on a source window, `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn` produces the ambient flat EOW seed directly. |
| Pointwise Jost overlap | Local OS-I section 4.5 equality `h45_source_eqOn` on the selected source neighborhood. |
| All-overlap branch laws | Proof-local `Word` and `Wadj` seeds on each nonempty local overlap, then checked `SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds`. |
| Gluing | Use checked `SCV.glued_iUnion` and differentiability helpers after the local branch laws are in hand. |
| Export | Produce `Hdiff` and the local horizontal zero representation consumed downstream. |

## Non-Circular Flat Transition

The flat transition is now fixed in this order:

1. Pull the flat common-edge test through the checked source cutoff and common
   edge linear equivalence.
2. Prove the source-side compact-test equality using
   `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick`.
3. For signed side source-test families, use
   `BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`
   to get the common source-side Schwinger limit uniformly on compact cone
   direction sets.
4. Prove the local pointwise source common-edge equality
   `h45_source_eqOn` for the ordinary `(4.1)` and transported genuine adjacent
   `(4.12)` analytic elements on the current source window.  This is now the
   live hard point.  It must use the corrected adjacent seed-to-Wick circuit,
   not the downstream deterministic adjacent carrier as upstream data.
5. Feed `h45_source_eqOn` into the checked non-circular flat bridge
   `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`.
   That theorem performs the zero-height compact-test equality, local EOW
   call, and quarter-turn transport without using `Hdiff`,
   `sourceRepresentsOn`, a common-boundary CLM, or the local `S'_n` branch.
6. Use the resulting ambient flat EOW seed as the flat crossover in the
   proof-local one-branch gallery.
7. Only after the `Hdiff` germ exists, use the common-boundary reducers such as
   `BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ` and
   `BHW.os45FlatCommonChart_commonBoundaryDifference_integral_zero_of_sourceRepresentsOn`.

Do not replace this with a finite side-height Schwinger identity.  Do not derive
`h414_integrals` from `Hdiff`, the common-boundary CLM, or the local SPrime
branch.

The earlier side-asymptotic transcript remains a valid analytic audit, but the
checked implementation has moved the immediate Lean consumer to the pointwise
source common-edge equality.  The two transfer blocks reduce further to the
same target:

```text
h45_source_eqOn on the current Figure-2-4 source window
```

The ordinary side uses the `(4.1)` branch normalized by
`ordinaryCommonEdge_metricBallChartInWindow`.  The adjacent side uses the
transported genuine `(4.12)` branch whose seed was shrunk into the
ordinary/adjacent initial-sector overlap.  This equality is not a wrapper: it
is the OS-I section 4.5 analytic identity needed before any `Hdiff`,
common-boundary CLM, or local `S'_n` branch exists.

The local support part of those targets is now checked: if the flat test is
supported in `os45CommonEdgeFlatCLE d n 1 '' Ulocal`, then for small positive
side height both signed cutoff-pulled source tests have support in `Ulocal`.
The remaining content is therefore the boundary-value convergence itself, not
support bookkeeping.

Immediate implementation boundary:

```text
h45_source_eqOn on the current Figure-2-4 source window
```

The first internal proof obligations for that equality are:

```lean
ordinary41_boundaryValue_uniform_on_sideCutoffTests
adjacent412_boundaryValue_uniform_on_sideCutoffTests
```

These are proof-local transfer blocks, not public theorem surfaces to assume
later.  They must
prove, from the ordinary `(4.1)` chain and the transported genuine `(4.12)`
chain respectively, that the branch-side signed side integrals are asymptotic
to the checked source-side signed pairings on the current local source window.
They may use the checked moving-support theorem
`D.toSideZeroDiagonalCLM_tsupport_subset_image_eventually` and the checked
source common-limit theorem
`D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`, and they
must feed the proof-local flat EOW step that produces `h45_source_eqOn`.

Do not introduce a public theorem whose hypotheses are
`hPlus_asymptotic`, `hMinus_asymptotic`, `h414_integrals`, an already built
`Wadj`, or an already built `Hdiff`: those hypotheses are exactly the
mathematical content still missing.  The next Lean edit should either prove
one of the two boundary-value transfer lemmas or add a neutral support lemma
used inside such a proof.

## Closure Queue

### Stage A: Local Figure 2-4 `Hdiff`

First close `BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`.

Implementation rule: add only support lemmas that expose or prove one of the
subtasks in the live blocker table.  If a proposed lemma merely repackages the
same missing analytic input, do not add it.

Lean frontier:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45BHWJostLocal.lean
```

Possible split rule: if the file becomes unwieldy, make a small companion file
for genuine SCV or Figure 2-4 local support.  The companion must have a narrow
mathematical purpose and a direct consumer in the `Hdiff` proof.

### Stage B: Common-Boundary CLM

After `Hdiff` exports local zero representation, prove the common-boundary CLM:

```lean
BHW.os45FlatCommonChart_commonBoundaryCLM_of_OSI45
```

This stage consumes local zero representation.  It is downstream from `Hdiff`
and must not be used to prove the flat transition inside `Hdiff`.

### Stage C: Local EOW Seed and SPrime Branch

Use the checked local EOW reducers to prove:

```lean
BHW.os45_BHWJost_localSPrimeEOWSeed_of_OSI45
BHW.os45_BHWJost_SPrimeBranchData_of_localSPrimeEOWSeedAt
```

Then call the accepted neutral theorem:

```lean
BHW.localSPrime_twoSectorBranch_of_EOW_BHW
```

The branch must use the common-edge seed selected by the OS45 local proof, not a
retired fixed-real-seed shortcut.

### Stage D: Pair Carrier

Build the OS45 source-patch pair carrier with the same local SPrime branch in
both slots:

```lean
BHW.os45_BHWJostPairData_on_figure24SourcePatch_of_OSI45
BHW.os45_BHWJostPairData_family_on_figure24SourcePatch_of_OSI45
```

This should be mechanical after Stage C and should not introduce new analytic
content.

### Stage E: Compact Wick/Jost Anchor

Consume the pair carrier:

```lean
BHW.os45CompactFigure24WickPairingEq_family_of_pairData_on_figure24SourcePatch
BHW.bvt_F_distributionalJostAnchor_of_pairData_on_figure24SourcePatch
```

This provides the exact source-patch compact Wick pairing and Jost anchor used
by the Hall-Wightman/PET step.

### Stage F: Hall-Wightman Source/PET

Prove the direct source/PET single-valuedness route:

```lean
BHW.HallWightmanPETSourceData
BHW.hallWightman_sourceScalarRepresentative_perm_invariant
BHW.hallWightman_petSourceData_of_distributionalAnchor
BHW.hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor
```

This stage must stay on the direct Hall-Wightman scalar-product route.  It
should not import the rejected descent routes.

### Stage G: Jost Boundary Limit

Prove the compactly supported Jost boundary-value limit:

```lean
bvt_F_jostBoundary_pairing_compact_tendsto_zero_of_spacelike_of_two_le
```

This is a boundary-limit theorem, not a finite-height equality theorem.

### Stage H: Boundary-Value Transfer to Locality

Transfer the compact Jost limit to adjacent locality:

```lean
bv_local_commutativity_transfer_of_swap_pairing_tendsto_compact
BHW.exists_compactSupportApprox_zeroOff_open
bvt_W_swap_pairing_of_spacelike_of_two_le
```

This is the E-to-R locality transfer after the analytic route is proved.

### Stage I: Low-Dimensional Branch

Handle the `d = 1` branch separately.  It must not use the `2 <= d` OS45 local
two-sector hull.

### Stage J: Final Theorem 2 Surface

Only after Stages A through I are checked, close the public Theorem 2 statement
in the E-to-R reconstruction chain.  No final wrapper should be added before
the analytic and boundary-value inputs above are complete.

## Next Proof-Doc Task

Before more Lean, finish the Lean-ready transcript for the `Wadj` branch-law
seed inside `BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`.
The active companion transcript is:

```text
docs/theorem2_wadj_branch_law_transcript.md
```

The transcript must specify:

1. The incoming and outgoing sheet domains for ordinary and adjacent local
   elements.
2. The local chart window and metric-ball data retained by each one-branch
   chain.
3. The exact ordinary-sector transfer step.
4. The exact adjacent-sector transfer step from the genuine `(4.12)` germ.
5. The flat real-Jost EOW transfer using the non-circular flat transition.
6. The proof-local overlap equality statement that produces each `Wadj`.
7. The identity-theorem propagation from `Wadj` and `Word` to the connected
   local core.
8. The final glued branch and horizontal zero representation exported by
   `Hdiff`.

Current correction: the adjacent `(4.12)` entry must be split into the raw seed
window at `zadj` and the transported usable initial chart at `zord`.  The
active transcript now names this proof-local output `hadj412`.  Its required
fields are now fixed: the transported branch `Badj412`, its ordinary-Wick
trace `hadj412_wick_trace`, its horizontal common-edge trace
`hadj412_common_trace`, and holomorphy on the connected initial-sector-overlap
window.  Lean work on the public producer should start only after that block,
the three transfer cases, and the all-overlap branch-seed fold have
theorem-surface-level statements and named inputs.

The focused transcript now expands the three formerly vague pre-Lean gaps into
proof-local Lean pseudocode:
`adjacent_sector_seed_transport`, `flat_zero_height_pairings_from_414`, and
`circuit_gallery_glue`.  The flat block is now corrected away from the
too-strong finite-side-height Schwinger route.  Arbitrary cone-direction
side-continuity remains checked support for later boundary-value statements,
but it is not the producer of the upstream flat `(4.14)` transition.

There are now two explicitly separated flat EOW uses.  The upstream use occurs
inside `hadj412`: it is the OS-I `(4.14)` compact-test boundary transfer from
the genuine adjacent `(4.12)` element to the ordinary common-edge side, and it
is what supplies `hadj412_common_trace`.  The downstream use occurs only after
`hadj412_wick_trace` and `hadj412_common_trace` have allowed
`BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3` to prove
`h45_source_eqOn`; at that later point the checked
`BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`
consumer gives the ambient flat EOW seed.  Do not call the downstream consumer
inside the upstream `hadj412` crossing, and do not replace the upstream
compact-test transfer by a theorem that assumes `h45_source_eqOn`, `Wadj`, or
`Hdiff`.

The upstream `(4.14)` transfer is a flat-chart statement, so the side families
coming from source variables must be scaled by
`(BHW.os45CommonEdgeFlatJacobianAbs n : ℂ)`.  The checked source-side theorem
gives an unscaled Schwinger limit in `NPointDomain` variables; the proof
transcript now applies the Jacobian before the filter-algebra step.  This keeps
the zero-height flat pairings aligned with the checked common-edge
change-of-variables lemmas.

The later identity-theorem step is also scoped narrowly.  It may propagate Wick
trace equality to the horizontal common edge only after the construction has
produced `Badj412` as a genuine single-valued holomorphic function on the same
connected open chart `Ucx` as `Ford`.  The connected-chart identity theorem
does not require simple connectivity; branch-selection and monodromy concerns
are discharged earlier by the one-branch gallery and the upstream flat EOW
seed.

The next genuine Lean target is the local OS-I transfer inside
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`: start from the raw
`(4.12)` seed window, transport that adjacent analytic element to the ordinary
Wick endpoint through the Figure-2-4 gallery, then use
`BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3` with `Badj412` as the adjacent
branch to propagate the E3 Wick equality to the horizontal common edge.  The
deterministic branch `z ↦ extendF (bvt_F OS lgc n) (permAct P.τ z)` may appear
only in `hadj412_common_trace`, after the genuine `(4.12)` element has been
transported to the endpoint-centered chart.  Then use the OS-I `(4.14)` flat
common-boundary compact-test equality at the horizontal edge, and only then
feed the resulting zero-height pairings into the checked local EOW bridge.
Adding a public theorem that merely assumes this transfer, `Wadj`, or `Hdiff`
is wrapper churn.

## Archive Pointers

Use these as references, not as the active control plane:

| File | Use |
| --- | --- |
| `docs/theorem2_locality_blueprint.md` | Full historical route record and detailed transcripts. |
| `docs/theorem2_wadj_branch_law_transcript.md` | Active companion transcript for the `Wadj` branch-law seed. |
| `docs/proof_docs_completion_plan.md` | Current proof-doc completion ledger and Stage-A transcript fragments. |
| `agents_chat.md` | Local coordination and route-correction log. |

Keep this file short.  If a section grows beyond a screen or two, move the
details to a companion transcript and leave only the target, status, and link
here.
