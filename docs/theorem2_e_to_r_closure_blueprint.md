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

Docs-first gate, 2026-05-16: do not resume Lean implementation of the
E-to-R/Theorem-2 critical path until the local OS-I `(4.14)` branch/source
transfer transcript is complete in
`docs/theorem2_wadj_branch_law_transcript.md`.  The required transcript is
the in-body proof of the two local side-height `have`s
`hPlus_asymptotic` and `hMinus_asymptotic`: ordinary `(4.1)` plus-sheet
pullback and moving boundary value; raw-adjacent `(4.12)` minus-sheet
pullback, raw-seed transport, and moving boundary value; checked source-side
common limit; then `SCV.eq_zeroHeight_of_common_sideLimit`.  No public
horizontal-pairing-zero wrapper or theorem assuming either asymptotic transfer
is allowed.

The raw adjacent `(4.12)` seed is the genuine OS-I seed window

```text
OmegaSeed412 =
  { z | BHW.permAct P.τ z in BHW.ForwardTube d n } inter H.OmegaJ

BSeed412 z =
  bvt_F OS lgc n (BHW.permAct P.τ z)
```

It is centered at the genuine adjacent seed
`zadj = BHW.permAct P.τ (gamma 0)`, not at the ordinary Wick endpoint
`zord = gamma 0`.  The usable adjacent initial data for the later one-branch
chain is the transported OS-I `(4.12)` element
`OmegaAdj0/BAdj0`, after the seed-to-Wick circuit has proved
`zord in OmegaAdj0` and
`BAdj0 zord = bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k)))`.
Thus `p0 = gamma 0` belongs to the transported initial data, not to the raw
seed window.  The false shortcut `zord in OmegaSeed412` is ruled out by the
checked nontriviality/seed-obstruction lemmas.

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
| Translated source-to-flat Jacobian algebra | Checked as `BHW.os45CommonEdgeFlatCLE_integral_comp_shift`. |
| Signed side source-test pointwise formula | Checked as `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_apply`. |
| Shifted/signed side cutoff removal | Checked as `BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge`, `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_of_tsupport_subset_edge`, `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_eventually`, and the source-window packet `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually`. |
| Signed side-height branch/source pullback | Checked as `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shift`, `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shiftedCLM`, `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM`, and `BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM`; this is pure coordinate/Jacobian/cutoff algebra and does not assume the OS-I `(4.14)` boundary-value limit. |
| Source-side side-sheet argument | Checked as `BHW.os45FlatCommonChartSourceSide`, `BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF`, and `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`; these name the exact source configuration obtained by undoing the quarter-turn, unfold the branch value to `extendF`, and identify the outgoing sheet-domain condition. |
| Eventual source-side sheet membership | Checked as `BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually`; for small positive side height, shifted support points land on the ordinary plus and raw-adjacent minus outgoing sheets. |
| Side branch integrability | Checked as `BHW.os45FlatCommonChart_branch_shifted_mul_integrable` and the compact-direction eventual package `BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually`; compact support plus side-domain membership gives the integrability input for the signed pullback theorem. |
| Signed side source-test common Schwinger limit | Checked as `BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`. |
| Local source-window side-test support | Checked as `BHW.os45FlatCommonChart_sideSupport_radius_sourceImage` and `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_tsupport_subset_image_eventually`. |
| Pure SCV moving-test boundary upgrade | Checked as `SCV.tube_boundaryValueData_moving_of_fixed` in `OSReconstruction/SCV/TubeBoundaryValues.lean`; use it only after the boundary CLM has already been selected. |
| Selected OS boundary-value moving-test upgrade | Checked as `bvt_boundary_values_moving` in `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`. |
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
| Flat transition | Two separated uses: upstream `hadj412` must prove the OS-I `(4.14)` source zero representation `hsource_zero_rep`, use the checked source-to-flat reducer, and call `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`; downstream, after `Badj412` exists on the connected chart, `h45_source_eqOn` may call `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`. |
| Pointwise Jost overlap | Local equality `h45_source_eqOn`, produced only after the transported genuine `(4.12)` branch has Wick and horizontal common-edge traces on the same connected chart as the ordinary branch. |
| All-overlap branch laws | Proof-local `Word` and `Wadj` seeds on each nonempty local overlap, then checked `SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds`. |
| Gluing | Use checked `SCV.glued_iUnion` and differentiability helpers after the local branch laws are in hand. |
| Export | Produce `Hdiff` and the local horizontal zero representation consumed downstream. |

## Non-Circular Flat Transition

The flat transition has two distinct layers, and they must stay separated.

1. **Upstream, inside `hadj412`.**  Choose the source window `Ulocal` and flat
   edge image
   `E = BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) '' Ulocal`.
   Prove the genuine OS-I `(4.14)` source zero representation for the current
   ordinary `(4.1)` element and the transported genuine adjacent `(4.12)`
   element:

   ```lean
   have hsource_zero_rep :
       SCV.RepresentsDistributionOn
         (0 : SchwartzMap (NPointDomain d n) Complex ->L[Complex] Complex)
         Ghoriz Ulocal := by
     -- OS-I `(4.14)` source common-boundary proof for the ordinary `(4.1)`
     -- and transported adjacent `(4.12)` analytic elements.
   ```

   Then feed `hsource_zero_rep` to the checked source-to-flat reducer
   `BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn`.
   It gives both zero-height fields against
   `Tlocal := BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P`; the
   proof-local equality `AdjEdge phi = OrdEdge phi` is only the transitivity of
   those two fields.  Feed `hzero_plus` and `hzero_minus` into
   `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`.
   This produces the upstream ambient seed and the endpoint field
   `hadj412_common_trace`.

2. **Downstream, after `hadj412`.**  Once the transported branch `Badj412` has
   both `hadj412_wick_trace` and `hadj412_common_trace` on the same connected
   chart as the ordinary branch, use
   `BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3` to obtain
   `h45_source_eqOn` on the source window.  Only then call
   `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`.

The checked source cutoff, source-pairing equality, signed source-test limit,
and support lemmas are useful coordinate audits.  They do not produce the
upstream source zero representation and must not be used as a disguised
zero-height normalization to the Wick or Schwinger anchor.

Do not replace the upstream proof with a finite side-height Schwinger identity.
Do not derive `h414_common_boundary`, `AdjEdge = OrdEdge`, or
`h414_integrals` from `Hdiff`, the common-boundary CLM, the local SPrime
branch, `h45_source_eqOn`, or the downstream source-common-edge bridge.

Immediate implementation boundary:

```text
hsource_zero_rep inside the upstream hadj412 flat real-Jost crossing
```

The first internal proof obligations are proof-local, not public theorem
surfaces:

```lean
let Ghoriz : NPointDomain d n -> Complex := fun u =>
  BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u)) -
    BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
      (1 : Equiv.Perm (Fin n))
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))

have hsource_zero_rep :
    SCV.RepresentsDistributionOn
      (0 : SchwartzMap (NPointDomain d n) Complex ->L[Complex] Complex)
      Ghoriz Ulocal := by
  -- exact OS-I `(4.14)` source common-boundary theorem for the current
  -- ordinary `(4.1)` element and transported genuine adjacent `(4.12)`
  -- element.  Prove local representations of the horizontal pulled-branch
  -- difference by the OS-I §4.5 source boundary leaf, then assemble them
  -- for every source test supported in `Ulocal` by
  -- `SCV.distribution_representation_of_local_representations_for_test`.

have hpairings_to_Tlocal :=
  BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn
    (d := d) hd OS lgc (P := P) hUlocal_sub hsource_zero_rep

have h414_common_boundary :
    exists T414 :
      SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex ->L[Complex] Complex,
      (forall phi, HasCompactSupport (phi : _ -> Complex) ->
        tsupport (phi : _ -> Complex) <= E ->
        OrdEdge phi = T414 phi) /\
      (forall phi, HasCompactSupport (phi : _ -> Complex) ->
        tsupport (phi : _ -> Complex) <= E ->
        AdjEdge phi = T414 phi) := by
  refine <Tlocal, hpairings_to_Tlocal.1, hpairings_to_Tlocal.2>

have h414_integrals :
    forall phi, HasCompactSupport (phi : _ -> Complex) ->
      tsupport (phi : _ -> Complex) <= E ->
      AdjEdge phi = OrdEdge phi := by
  intro phi hphi_compact hphiE
  obtain <T414, hOrd_T414, hAdj_T414> := h414_common_boundary
  exact (hAdj_T414 phi hphi_compact hphiE).trans
    (hOrd_T414 phi hphi_compact hphiE).symm
```

After `hsource_zero_rep` is proved, the fields of `h414_common_boundary` are
mechanical via the checked source-to-flat reducer above.  The only remaining
mathematics in the upstream flat transfer is therefore the OS-I source
zero-representation theorem itself, not a new flat `T414` packet.

The companion transcript expands that theorem as a proof body: for an
arbitrary source test supported in `Ulocal`, cover its support by local
precompact windows, assemble those local representations with
`SCV.distribution_representation_of_local_representations_for_test`, and prove
the local leaf by the OS-I §4.5 boundary-value transfer from the ordinary and
raw transported adjacent analytic branches to the horizontal common-edge
pulled-branch difference.  The transfer keeps the real/flat test on the
boundary and shifts the analytic branches by side heights tending to zero; it
does not manufacture a finite-height compact Wick replacement test.  That leaf
uses the ordinary `(4.1)` endpoint, the retained raw `(4.12)` adjacent chain,
and the `(4.14)` Lorentz-covariance input.  It must not call the later
`Hdiff` reducer, the flat EOW bridge, `Wadj`, or a public
`h414_common_boundary` wrapper.  Deep Research interaction
`v1_ChdtVklJYXN1V0E2S1AyOG9QbjdlaTZBYxIXbVZJSWFzdVdBNktQMjhvUG43ZWk2QWM`
completed on 2026-05-16 and confirms this leaf is non-circular only in the
direct OS-I sense: `hhorizontal_zero` must be proved by a
Fourier-Laplace/Jost rotation using `(4.1)`, raw transported `(4.12)`, and
`(4.14)` covariance.  It must not be proved by constructing `Hdiff` first and
then reading off its horizontal trace.

Current sharpening: the side-to-Schwinger fixed-direction route is overstrong
when used as a public shortcut for the flat real common edge, and is not the
exported Stage-A target.  As a primitive theorem surface it would
try to prove

```lean
OrdEdge = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
  OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi)

AdjEdge = (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
  OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi)
```

for the zero-height flat edge pairings directly from source Wick-section
normalization.  That is the rejected Schwinger-CLM shortcut.  The source
Wick-section pairing theorems normalize the source analytic element; they do
not by themselves identify the zero-height flat common-boundary CLM with
`OS.S`.  Such individual equalities are admissible only as proof-local
consequences of the side-height branch/source asymptotic transfers plus the
checked common side-limit algebra.

The direct Lean target inside the flat block is instead

```lean
AdjEdge = OrdEdge
```

for the ordinary and selected-adjacent zero-height flat branch pairings against
the same compactly supported flat test.  The tempting proof by two individual
direct pullbacks to the Wick/source pairings is retired: it is the same
category mistake in a less obvious costume unless those pullbacks are derived
from the boundary-limit transfer.  The Wick/source pairing equality
`BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick` is a checked
Wick-seed equality for the source analytic elements; it does not identify the
zero-height flat real common-boundary pairings with those Wick pairings.

The live mathematical subclaim is the OS-I section 4.5 source
zero-representation behind the common-boundary distribution:

```lean
have hsource_zero_rep :
    SCV.RepresentsDistributionOn
      (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ)
      Ghoriz Ulocal := by
  -- OS-I `(4.14)` source common-boundary proof for the current ordinary
  -- `(4.1)` and transported adjacent `(4.12)` analytic elements.
```

Then the checked
`BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn`
turns `hsource_zero_rep` into both flat zero-height pairings against
`Tlocal := BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P`.  Packaging
those two fields as `h414_common_boundary` is proof-local bookkeeping; a
public theorem assuming `h414_common_boundary`, either zero-height equality, or
an already built adjacent `Tlocal` representation remains a wrapper.

Deep Research interaction
`v1_ChdtVVlJYXQzOEJybTBuc0VQZ2UyRDJROBIXbVVZSWF0MzhCcm0wbnNFUGdlMkQyUTg`
completed on 2026-05-16 and confirms this theorem shape: Option B,
common-boundary `AdjEdge = OrdEdge`, is the mathematically correct target;
individual zero-height normalization to the Wick/Schwinger anchor is
category-confused and circular for the strict OS-I locality proof when used as
an assumed primitive rather than as the final consequence of the side-height
limit proof.

Deep Research interaction
`v1_Chc5VmdJYXEtV01JeUx4TjhQcXBmbndBURIXOVZnSWFxLVdNSXlMeE44UHFwZm53QVE`
completed on 2026-05-16 and independently rejects the finite-height compact
`chiWick` helper.  The replacement theorem shape is the boundary-limit route:
define ordinary and adjacent side-height branch pairings against the original
test, prove their `(4.14)` branch/source asymptotic transfers, combine with
the checked source-side common Schwinger limit, and take the zero-height
common limit.  This confirms that the two asymptotic transfers, not a test
transform, are the genuine gap.

Do not introduce a public theorem whose hypotheses are
`hPlus_asymptotic`, `hMinus_asymptotic`, either fixed-direction asymptotic,
`h414_common_boundary`, `h414_integrals`, an already built `Wadj`, or an
already built `Hdiff`: those hypotheses are exactly the mathematical content
still missing.  The next Lean edit should prove the local common-boundary
distribution inside `BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`;
it should not add a new side-to-Schwinger wrapper.

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

Update 2026-05-16: the active companion transcript now spells out the
`hpair_seed` case split.  The ordinary-sector seed is local equality with the
ordinary global branch; the adjacent-sector seed is a retained finite gallery
back to the genuine `hadj412` output; the flat real-Jost seed is the only case
that consumes the OS-I `(4.14)` source zero representation and then calls the
checked local zero-height bridge.  None of these should be surfaced as public
wrappers before their proof bodies are complete.

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
the adjacent-sector seed transport, the flat zero-height pairing block, and
circuit gallery gluing.  These are local proof blocks, not public theorem
wrappers.  The flat block is now corrected away from the
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

The upstream `(4.14)` transfer is a flat-chart statement, so any use of
source-coordinate change-of-variables must keep the factor
`(BHW.os45CommonEdgeFlatJacobianAbs n : ℂ)` explicit.  Those source-side
lemmas are bookkeeping for comparing coordinate descriptions; they are not the
producer of `hsource_zero_rep` and they do not identify the flat zero-height
pairing with a Schwinger or Wick anchor.

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
Wick endpoint through the Figure-2-4 gallery, and prove the upstream OS-I
`(4.14)` source zero representation at the flat crossing to obtain
`hadj412_common_trace` via the checked source-to-flat reducer.  Only after the
genuine `(4.12)` element has both Wick and common-edge traces should the proof use
`BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3` with `Badj412` as the adjacent
branch to obtain `h45_source_eqOn`; that downstream equality then feeds the
checked source-common-edge flat bridge.  The upstream flat crossing itself
uses `hsource_zero_rep` and the checked source-to-flat reducer, not a public
common-boundary packet.  The deterministic branch
`z ↦ extendF (bvt_F OS lgc n) (permAct P.τ z)` may appear only in
`hadj412_common_trace`, after the raw seed has been transported to the
endpoint-centered chart.  Adding a public theorem that merely assumes this
transfer, `Wadj`, or `Hdiff` is wrapper churn.

Gemini `gemini-3.1-pro-preview` audit on 2026-05-16 independently rejected the
tempting initial-overlap shortcut
`Fadj z := extendF (bvt_F OS lgc n) (permAct P.τ z)`.  For the strict route,
that definition is downstream endpoint identification, not upstream adjacent
branch data.  The live implementation must therefore continue to construct
`Badj412` from the raw `(4.12)` seed, prove the OS-I `(4.14)` flat boundary
transfer, transport equality through the finite Figure-2-4 gallery, and only
after that rewrite the endpoint as the deterministic permuted branch.

Lean-entry correction after the compact-test audit: before editing the big
local file, the proof transcript must expose the direct boundary-limit theorem
used in `hhorizontal_zero`.  Do **not** implement the earlier finite-height
`chiWick` helper; the completed compact-test audit rejects that theorem shape.
Ordinary distributional analytic continuation gives side-height limits, not a
literal compactly supported Wick-side replacement test.

The pure moving-test/Banach-Steinhaus layer is no longer a live theorem-2
blocker: `SCV.tube_boundaryValueData_moving_of_fixed` proves the moving-test
upgrade for an already-selected tube boundary functional, and
`bvt_boundary_values_moving` specializes it to the selected OS witness
`bvt_F/bvt_W`.  The remaining mathematical gap is narrower and sharper: prove
the OS-I branch/source asymptotic transfers for the ordinary `(4.1)` and
transported raw adjacent `(4.12)` side-height families, then combine them with
the checked source-side Schwinger common limit and checked side-limit algebra
to obtain `AdjEdge = OrdEdge`.  Individual zero-height-to-Schwinger
normalizations are not the primitive Stage-A target.

Current proof-doc gate status: the active Wadj transcript now expands the
coordinate and moving-test layers down to local `have`s.  The two exact places
that still carry genuine OS-I content are:

```lean
hOrd_fixed
hOrd_source_norm
hAdj_fixed
hAdj_source_norm
```

These are not wrapper names.  They are proof-local obligations inside
`hPlus_asymptotic_eta0` and `hMinus_asymptotic_eta0`.  Their shared contract is:
select the boundary functional from the current one-branch analytic element,
prove fixed-test side-height convergence on the correct sheet, upgrade it to
the moving cutoff-pulled source tests, then identify the selected boundary
functional with the Figure-2-4 source pairing.  For the ordinary side the
incoming sheet is `BHW.ExtendedTube d n`; for the raw-adjacent side it is the
transported `(4.12)` seed window
`{z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ`.
The adjacent endpoint formula `extendF (bvt_F OS lgc n) (BHW.permAct P.τ z)`
may be used only after this raw analytic element has reached the terminal
endpoint chart.

Deep Research terminology guard: the asymptotic transfers themselves should
be derived from individual moving side-height boundary-value limits for the
two branch families, with the OS-II temperedness/growth guard included before
subtraction.  That is not the retired shortcut.  The retired shortcut is a
static zero-height flat-edge normalization directly to the Wick/Schwinger
anchor, bypassing the side-height branch/source comparison.

Code-level audit after the deterministic-adjacent shortcut check:
`extendF (bvt_F OS lgc n) (BHW.permAct P.τ z)` is holomorphic on the downstream
permuted extended-tube sector and matches the raw seed on the preimage-forward
tube where `extendF_eq_on_forwardTube` applies.  This does not close the live
gap.  In Stage A it may appear only after the raw `(4.12)` analytic element has
been transported to the terminal endpoint; using it as the upstream adjacent
chain is the rejected shortcut.  The next real proof leaf is still the pair of
ordinary and raw-adjacent `(4.14)` branch/source asymptotic transfers, not
another public reduction theorem.

No new helper should be introduced on this turn.  The zero conclusion must be
proved in the body of the upstream `hadj412` flat real-Jost crossing for the
current compact source/flat test.  Factoring out a theorem before the two
asymptotic transfers are proved is wrapper churn, even if the theorem's final
conclusion is a zero integral.

The in-body Lean target remains the two proof-local asymptotic transfers:

```lean
-- proof-local shape, ordinary side
TendstoUniformlyOn
  (fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
  (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
  (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta

-- proof-local shape, transported raw adjacent side
TendstoUniformlyOn
  (fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
  (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
  (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta
```

The ordinary proof input is the endpoint-centered `(4.1)` one-branch chain.
Its incoming sheet is the ordinary extended-tube branch
`BHW.extendF (bvt_F OS lgc n)` on `BHW.ExtendedTube d n`; its outgoing sheet
is the flat plus side
`BHW.os45FlatCommonChartOmega d n 1`.  The adjacent proof input is the raw
`OmegaSeed412/BSeed412` chain transported to the endpoint.  Its incoming sheet
is
`{z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ`
with branch `fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)`; its
outgoing sheet is the selected flat minus side
`BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)`.  Deterministic
`extendF o permAct` is permitted only after the raw chain has reached the
terminal endpoint chart.

Both transfers must be proved from the same three local ingredients:

1. side-window membership from
   `BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24`, giving the
   ordinary plus and selected adjacent minus sheet domains for all small
   positive heights and all `eta in Keta`;
2. the checked branch integral pullback
   `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM`
   plus `D.toSideZeroDiagonalCLM_apply`/support removal, which identifies the
   exact moving source test under the flat CLE and Jacobian;
3. the OS-I `(4.14)` Fourier-Laplace covariance/boundary-value theorem,
   applied to the ordinary `(4.1)` analytic element and to the transported raw
   adjacent `(4.12)` analytic element, with the existing moving-test upgrade
   only after the correct boundary functional has been selected.

The checked source-side Schwinger limits and
`SCV.eq_zeroHeight_of_common_sideLimit` are downstream algebra.  They are not
allowed to serve as substitutes for either `(4.14)` branch/source transfer.

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
