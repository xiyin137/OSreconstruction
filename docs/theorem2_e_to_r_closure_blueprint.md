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

Do not introduce new trust boundaries or proof stubs.  The only accepted
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

Transcript checkpoint, 2026-05-17: the companion transcript now includes the
direct local zero-height pairing body, the ordinary/raw-adjacent side-height
transfer order, the all-overlap branch-seed case split, compact-collar endpoint
DCT, and current-test terminal normalizations.  This identifies the intended
direct producer shape only; it is not a closure declaration.  Lean work must
still start with those in-body proofs and must not introduce wrapper theorem
surfaces.

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
| Signed side-height branch/source pullback | Checked as `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shift`, `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shiftedCLM`, `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM`, `BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM`, and the fixed-test translated-test form `BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest`; this is pure coordinate/Jacobian/cutoff algebra plus test-translation cancellation and does not assume the OS-I `(4.14)` boundary-value limit. |
| Source-side side-sheet argument | Checked as `BHW.os45FlatCommonChartSourceSide`, `BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF`, and `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`; these name the exact source configuration obtained by undoing the quarter-turn, unfold the branch value to `extendF`, and identify the outgoing sheet-domain condition. |
| Eventual source-side sheet membership | Checked as `BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually`; for small positive side height, shifted support points land on the ordinary plus and raw-adjacent minus outgoing sheets. |
| Side branch integrability | Checked as `BHW.os45FlatCommonChart_branch_shifted_mul_integrable` and the compact-direction eventual package `BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually`; compact support plus side-domain membership gives the integrability input for the signed pullback theorem. |
| Inverse-CLE fixed-test support | Checked as `BHW.hasCompactSupport_comp_os45CommonEdgeFlatCLE_symm`, `BHW.tsupport_comp_os45CommonEdgeFlatCLE_symm_subset_edgeSet`, and the bundled packet `BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM_flatPullback_support`; these are support-only lemmas for the auxiliary `psi0Flat` used in scalar cancellation. |
| Fixed source-side scalar cancellation | Checked as `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest`; after the selected flat translated-test limit is proved from the raw OS-I fixed theorem, this support theorem applies the translated-test pullback and cancels the positive flat Jacobian.  It does not select `Word`/`Wadj`, assert a boundary CLM, or identify the moving Figure-2-4 side tests. |
| Compact-support moving-test convergence | Checked as `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport` and the assembled moving-test theorem `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport`; for the genuine `sourceSide` path, eventual common compact support plus zeroth Schwartz-seminorm convergence move a compactly supported source test from the selected fixed endpoint limit to the moving side-test limit.  The concrete Figure-2-4 side-test inputs are checked as `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually` and `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero`; the fixed-height product integrability used by the split is checked as `BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport` with an eventual fixed-test companion `BHW.eventually_integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport`. |
| Signed side source-test common Schwinger limit | Checked as `BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`. |
| Local source-window side-test support | Checked as `BHW.os45FlatCommonChart_sideSupport_radius_sourceImage` and `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_tsupport_subset_image_eventually`. |
| Pure SCV moving-test boundary upgrade | Checked as `SCV.tube_boundaryValueData_moving_of_fixed` in `OSReconstruction/SCV/TubeBoundaryValues.lean`; use it only after the boundary CLM has already been selected. |
| Selected OS boundary-value moving-test upgrade | Checked as `bvt_boundary_values_moving` in `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`. |
| Pointwise source common-edge to flat zero-height bridge | Checked as `BHW.os45FlatCommonChart_zeroHeight_pairings_eq_of_sourceCommonEdge_eqOn`. |
| Pointwise source common-edge to ambient flat EOW seed | Checked as `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`. |
| Initial and endpoint metric-ball continuation charts | Checked as `BHW.OS45BHWJostHullData.ordinaryWick_metricBallChartInWindow`, `BHW.OS45BHWJostHullData.OS412SeedWindow_metricBallChartInWindow`, the two-sheet raw-seed shrink `BHW.OS45BHWJostHullData.OS412SeedWindow_initialSectorOverlap_metricBallChart`, `BHW.OS45BHWJostHullData.ordinaryCommonEdge_metricBallChartInWindow`, `BHW.OS45BHWJostHullData.adjacentCommonEdge_metricBallChartInWindow`, and `BHW.OS45BHWJostHullData.commonEdgeDifference_metricBallChartInWindow`.  Private pointed adapters for the Wick, raw-seed, ordinary endpoint, adjacent endpoint, and endpoint-difference metric-ball charts are checked in `OSToWightmanLocalityOS45Figure24Hdiff.lean`.  The raw seed-to-ordinary-Wick carrier support is checked as `BHW.OS45BHWJostHullData.OS412Seed_ordinaryWick_connectedNeighborhood` and `BHW.OS45BHWJostHullData.OS412Seed_ordinaryWick_endpointMetricBall`; arbitrary two-sheet corridor carriers are checked as `BHW.initialSectorOverlap_connectedNeighborhood_of_joinedIn` and `BHW.initialSectorOverlap_endpointMetricBall_of_joinedIn`. |
| Endpoint-centered holomorphic chart restriction | Checked as `SCV.exists_metric_ball_differentiableOn_subset_of_mem_open`; after a chart carrier is open and contains the selected overlap or endpoint point, this gives a centered metric ball inside the carrier and preserves `DifferentiableOn` on the restricted ball. |
| Local reachability to finite chain | Checked as `SCV.reachable_eq_univ_of_local_symmetric_extension`; once the OS-I local transfer cases propagate a reachable chain inside a small open time-window, this neutral theorem turns the nonempty reachable set in `unitInterval` into all of `unitInterval`.  It contains no OS/BHW branch equality. |
| All-overlap metric-ball identity propagation | Checked as `SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds`. |
| Common-model overlap seed | Checked as `SCV.local_overlap_seed_of_common_model` and pointed variant `SCV.local_overlap_seed_at_of_common_model`; ordinary-sector overlaps can use this directly when both local charts agree with `OrdGlobal` on their carriers and the selected overlap point must belong to the seed. |
| Common side-limit zero-height equality | Checked as `SCV.eq_zeroHeight_of_common_sideLimit`. |
| Singleton fixed-direction uniform bridge | Checked as `SCV.tendstoUniformlyOn_singleton_iff_tendsto`; after the ordinary or raw-adjacent fixed-direction side-height transfer is proved at `eta0`, this is the only bridge needed to feed the singleton compact direction set into `SCV.eq_zeroHeight_of_common_sideLimit`. |
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

The first hard implementation block is the adjacent all-overlap `Wadj`
branch-law seed.  The ordinary side `Word` and adjacent side `Wadj` must be
produced while the proof-local finite-chain data is still in scope.  They must
be genuine ambient
complex-open overlap seeds, with metric-ball witnesses suitable for the checked
SCV identity helpers.

The direct proof must supply:

| Subtask | Required content |
| --- | --- |
| Ordinary analytic element | OS-I `(4.1)` local branch and Wick normalization. |
| Adjacent analytic element | Corrected OS-I `(4.12)` local branch from the genuine adjacent initial germ. |
| Local transfer along gamma | Case split into ordinary-sector, adjacent-sector, and flat real-Jost EOW transition. |
| Flat transition | Two separated uses: upstream `hadj412` must prove the OS-I `(4.14)` local zero-height pairings `hzero_plus`/`hzero_minus` directly from ordinary/raw-adjacent side-height branch/source transfers plus the checked common source limit, then call `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`; downstream, after `Badj412` exists on the connected chart, `h45_source_eqOn` may call `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`. |
| Pointwise Jost overlap | Local equality `h45_source_eqOn`, produced only after the transported genuine `(4.12)` branch has Wick and horizontal common-edge traces on the same connected chart as the ordinary branch. |
| All-overlap branch laws | Proof-local `Word` and `Wadj` seeds on each nonempty local overlap, then checked `SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds`. |
| Gluing | Use checked `SCV.glued_iUnion` and differentiability helpers after the local branch laws are in hand. |
| Export | Produce `Hdiff` and the local horizontal zero representation consumed downstream. |

## Non-Circular Flat Transition

The flat transition has two distinct layers, and they must stay separated.

1. **Upstream, inside `hadj412`.**  Choose the source window `Ulocal` and flat
   edge image
   `E = BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) '' Ulocal`.
   Prove the genuine OS-I `(4.14)` local zero-height pairings for the current
   ordinary `(4.1)` element and transported genuine adjacent `(4.12)` element:

   ```lean
   let Tlocal := BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P

   have hzero_plus :
       forall phi, HasCompactSupport (phi : _ -> Complex) ->
         tsupport (phi : _ -> Complex) <= E ->
         integral (fun x =>
           BHW.os45FlatCommonChartBranch d n OS lgc
             (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex)) * phi x)
           = Tlocal phi := by
     -- ordinary `(4.1)` plus-side branch/source transfer,
     -- endpoint DCT, checked common source limit, and
     -- `zeroHeight_pairings_eq_common_of_sideLimits`.

   have hzero_minus :
       forall phi, HasCompactSupport (phi : _ -> Complex) ->
         tsupport (phi : _ -> Complex) <= E ->
         integral (fun x =>
           BHW.os45FlatCommonChartBranch d n OS lgc
             (P.τ.symm * (1 : Equiv.Perm (Fin n)))
             (fun a => (x a : Complex)) * phi x)
           = Tlocal phi := by
     -- retained raw `(4.12)` minus-side branch/source transfer,
     -- endpoint DCT, checked common source limit, and
     -- `zeroHeight_pairings_eq_common_of_sideLimits`.
   ```

   Feed `hzero_plus` and `hzero_minus` directly into
   `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`.
   This produces the upstream ambient seed and the endpoint field
   `hadj412_common_trace`.  Do not insert an intermediate source-window
   representation packet.

2. **Downstream, after `hadj412`.**  Once the transported branch `Badj412` has
   both `hadj412_wick_trace` and `hadj412_common_trace` on the same connected
   chart as the ordinary branch, use
   `BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3` to obtain
   `h45_source_eqOn` on the source window.  Only then call
   `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`.

The checked source cutoff, source-pairing equality, signed source-test limit,
and support lemmas are useful coordinate audits.  They do not produce the
upstream zero-height pairings by themselves and must not be used as a disguised
finite-height normalization to the Wick or Schwinger anchor.

Do not replace the upstream proof with a finite side-height Schwinger identity.
Do not derive the local common-boundary packet, `AdjEdge = OrdEdge`, or the
flat `(4.14)` integral equality from `Hdiff`, the common-boundary CLM, the
local SPrime branch, `h45_source_eqOn`, or the downstream source-common-edge
bridge.

Immediate implementation boundary:

```text
hzero_plus / hzero_minus inside the upstream hadj412 flat real-Jost crossing
```

The first internal proof obligations are proof-local, not public theorem
surfaces:

```lean
have hzero_pairings :
    (forall phi, HasCompactSupport (phi : _ -> Complex) ->
      tsupport (phi : _ -> Complex) <= E -> OrdEdge phi = Tlocal phi) /\
    (forall phi, HasCompactSupport (phi : _ -> Complex) ->
      tsupport (phi : _ -> Complex) <= E -> AdjEdge phi = Tlocal phi) := by
  -- For each compact flat test:
  --   1. prove zero-height side continuity to the literal endpoint scalars
  --      `cPlus := OrdEdge phi` and `cMinus := AdjEdge phi` by
  --      `SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing`;
  --   2. prove ordinary plus branch/source asymptotic transfer;
  --   3. prove raw-adjacent minus branch/source asymptotic transfer;
  --   4. combine each transfer with the checked source-side common limit,
  --      rewritten to the current `cCommon := Tlocal phi`;
  --   5. call `zeroHeight_pairings_eq_common_of_sideLimits`.
```

The local `AdjEdge = OrdEdge` proof is just transitivity through `Tlocal`.  Do
not insert an intermediate source-representation, public common-boundary
carrier, or wrapper.

The exact scalar-limit skeleton inside the preceding `intro phi hphi_compact
hphiE` block is:

```lean
let l := 𝓝[Set.Ioi 0] (0 : ℝ)
let σAdj := P.τ.symm * (1 : Equiv.Perm (Fin n))
let Kη : Set (BHW.OS45FlatCommonChartReal d n) := {eta0}
have hKη_nonempty : Kη.Nonempty := ⟨eta0, by simp [Kη]⟩

let Fplus : ℝ -> BHW.OS45FlatCommonChartReal d n -> ℂ := fun eps eta =>
  ∫ x : BHW.OS45FlatCommonChartReal d n,
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
      (fun a => (x a : ℂ) +
        (eps : ℂ) * (eta a : ℂ) * Complex.I) * phi x

let Fminus : ℝ -> BHW.OS45FlatCommonChartReal d n -> ℂ := fun eps eta =>
  ∫ x : BHW.OS45FlatCommonChartReal d n,
    BHW.os45FlatCommonChartBranch d n OS lgc σAdj
      (fun a => (x a : ℂ) -
        (eps : ℂ) * (eta a : ℂ) * Complex.I) * phi x

let cPlus : ℂ := OrdEdge phi
let cMinus : ℂ := AdjEdge phi
let cCommon : ℂ := Tlocal phi

have hplus_zero :
    TendstoUniformlyOn Fplus (fun _ => cPlus) l Kη := by
  -- Use the neutral theorem directly with `Tφ := cPlus` and
  -- `hzero := by rfl`.  Do not call
  -- `_of_zeroHeight_pairingCLM` here: that theorem requires the equality
  -- `OrdEdge phi = T phi` that this block is proving.
  exact SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
    hΩplus_open
    (BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n)))
    hFplus_cont hplus_real_mem
    (1 : ℝ) hplus_side Kη hKη_compact hKη_cone
    phi hphi_compact hphiE cPlus (by rfl)

have hminus_zero :
    TendstoUniformlyOn Fminus (fun _ => cMinus) l Kη := by
  exact SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
    hΩminus_open
    (BHW.os45FlatCommonChartBranch d n OS lgc σAdj)
    hFminus_cont hminus_real_mem
    (-1 : ℝ) hminus_side Kη hKη_compact hKη_cone
    phi hphi_compact hphiE cMinus (by rfl)

have hplus_common :
    TendstoUniformlyOn Fplus (fun _ => cCommon) l Kη := by
  -- `hPlus_asymptotic_eta0`, lifted to the singleton `Kη`, plus the checked
  -- source common limit and the ordinary-edge CLM/source normalization.
  exact hplus_branch_source_to_Tlocal

have hminus_common :
    TendstoUniformlyOn Fminus (fun _ => cCommon) l Kη := by
  -- Same shape, but the branch endpoint comes from retained raw `(4.12)`
  -- terminal provenance before the `extendF o permAct` endpoint rewrite.
  exact hminus_branch_source_to_Tlocal

have hscalars : cPlus = cCommon ∧ cMinus = cCommon :=
  zeroHeight_pairings_eq_common_of_sideLimits
    hKη_nonempty hplus_zero hminus_zero hplus_common hminus_common
```

The remaining hard bodies in this scalar skeleton are exactly
`hplus_branch_source_to_Tlocal` and `hminus_branch_source_to_Tlocal`: they are
the ordinary and retained raw-adjacent side-height branch/source transfers,
followed by the checked source common limit and the ordinary-edge
CLM/source-normalization rewrite.  A theorem that takes either of those two
transfers, `cPlus = cCommon`, `cMinus = cCommon`, or `AdjEdge = OrdEdge` as a
hypothesis is still a wrapper and is off-route.

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
common-boundary wrapper.  Deep Research interaction
`v1_ChdtVklJYXN1V0E2S1AyOG9QbjdlaTZBYxIXbVZJSWFzdVdBNktQMjhvUG43ZWk2QWM`
completed on 2026-05-16 and confirms this leaf is non-circular only in the
direct OS-I sense: `hhorizontal_zero` must be proved by a
Fourier-Laplace/Jost rotation using `(4.1)`, raw transported `(4.12)`, and
`(4.14)` covariance.  It must not be proved by constructing `Hdiff` first and
then reading off its horizontal trace.

The arbitrary local source-test contraction is now fixed in the companion
transcript.  Given `chi` supported in the local source window `V`, set
`e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))` and

```lean
let phiChi :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm) chi
```

Then prove `hphiChi_compact`, `hphiChi_image : tsupport phiChi <= e '' V`,
`hphiChiUlocal : tsupport phiChi <= e '' Ulocal`, and `hphiChiE` by
`BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff`, and the pointwise cutoff-removal
identity

```lean
forall u,
  (D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) phiChi :
    NPointDomain d n -> Complex) u = chi u
```

by `D.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge`.  The side-height
OS-I leaf is then applied in-body to `phiChi`, producing the flat zero.  The
checked theorem
`BHW.os45FlatCommonChart_commonBoundaryDifference_integral_eq_sourcePullback`
rewrites that flat zero to
`(BHW.os45CommonEdgeFlatJacobianAbs n : Complex) * integral (Ghoriz * chi)`,
and `BHW.os45CommonEdgeFlatJacobianAbs_pos` removes the nonzero Jacobian.
This is the only permitted route from the local flat side-height equality back
to the arbitrary source pairing.

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

The live mathematical subclaim is now the OS-I section 4.5 local zero-height
pairing block behind the common-boundary distribution:

```lean
have hzero_plus :
    ∀ phi, HasCompactSupport (phi : _ → ℂ) →
      tsupport (phi : _ → ℂ) ⊆ E →
      OrdEdge phi = Tlocal phi := by
  -- ordinary `(4.1)` side-height branch/source transfer.

have hzero_minus :
    ∀ phi, HasCompactSupport (phi : _ → ℂ) →
      tsupport (phi : _ → ℂ) ⊆ E →
      AdjEdge phi = Tlocal phi := by
  -- retained raw-adjacent `(4.12)` side-height branch/source transfer.
```

The proof should derive `AdjEdge = OrdEdge` directly from those two fields by
transitivity through `Tlocal`; inserting a named source-representation or
common-boundary packet here is avoidable wrapper churn.

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
the local common-boundary packet, the flat `(4.14)` integral equality, an
already built `Wadj`, or an already built `Hdiff`: those hypotheses are exactly
the mathematical content still missing.  The next Lean edit should prove the
local common-boundary distribution inside
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`; it should not add a
new side-to-Schwinger wrapper.

## Closure Queue

### Stage A: Local Figure 2-4 `Hdiff`

First close `BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`.

Implementation rule: add only support lemmas that expose or prove one of the
subtasks in the live blocker table.  If a proposed lemma merely repackages the
same missing analytic input, do not add it.

Lean frontier:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

File-placement rule: do not import `OSToWightmanLocalityOS45SourceSideMoving`
back into `OSToWightmanLocalityOS45BHWJostLocal.lean`, because the source-side
support stack already imports through `BHWJostLocal`.  The producer
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` should therefore live
in a downstream narrow companion file that imports the checked BHW/Jost local
geometry and the checked SourceSide support.  The companion must contain the
direct `Hdiff` proof and any proof-local witnesses needed by it, not a consumer
wrapper around an already assumed `Hdiff`.

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

## Proof-Doc Gate Before Lean

The active transcript for the `Wadj` branch-law seed inside
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` is now the control
plane for implementation.  Before any Lean edit, rerun the route and
diff-hygiene scans on this file and the companion transcript.  The active
companion transcript is:

```text
docs/theorem2_wadj_branch_law_transcript.md
```

The implementation must keep the transcript's proof-local objects available:

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
that consumes the OS-I `(4.14)` local zero-height pairings and then calls the
checked local zero-height bridge.  None of these should be surfaced as public
wrappers before their proof bodies are complete.

The adjacent-sector seed must be overlap-centered, not merely chain-labeled.
Given two retained adjacent terminal charts and a point
`z0 ∈ A.terminalCarrier ∩ B.terminalCarrier`, the checked private consumer
retargets both terminal charts to metric balls centered at `z0`.  The proof
must then supply the `hgrid` contract: for arbitrary such restrictions, build a
`PointedCommonCenterGalleryPair` whose `left 0` and `right 0` are the two
restrictions.  The consumer returns the required
`Set.EqOn A.branch B.branch W`, with `z0 ∈ W`.  The local chart is never defined
as `extendF o permAct`; that formula is only a transported endpoint rewrite
after the genuine `(4.12)` chain has reached the endpoint.

Current correction: the adjacent `(4.12)` entry must be split into the raw seed
window at `zadj` and the transported usable initial chart at `zord`.  The
active transcript now names this proof-local output `hadj412`.  Its required
fields are now fixed: the transported branch `Badj412`, its ordinary-Wick
trace `hadj412_wick_trace`, its horizontal common-edge trace
`hadj412_common_trace`, and holomorphy on the connected initial-sector-overlap
window.  The Lean-entry contract is to implement that block, the three transfer
cases, the terminal current-test normalizations, and the all-overlap branch-seed
fold as proof-local bodies with the named inputs in the companion transcript.

The focused transcript now expands the three formerly vague pre-Lean gaps into
proof-local Lean pseudocode:
the adjacent-sector seed transport, the flat zero-height pairing block, and
circuit gallery gluing.  These are local proof blocks, not public theorem
wrappers.  The flat block is now corrected away from the
too-strong finite-side-height Schwinger route.  Arbitrary cone-direction
side-continuity remains checked support for later boundary-value statements,
but it is not the producer of the upstream flat `(4.14)` transition.

Lean-entry correction note, 2026-05-17: a pinned Deep Research audit
(`deep-research-max-preview-04-2026`, interaction
`v1_ChZEZ1FKYW9pWEFjYTV4TjhQd2QtWU9BEhZEZ1FKYW9pWEFjYTV4TjhQd2QtWU9B`)
confirmed that the overlap-centered adjacent seed route is valid only if the
proof supplies explicit local path-independence data.  The transcript must not
treat "same raw `(4.12)` seed plus same endpoint" as a proof of uniqueness.
The Wadj transcript now contains the proof-local restricted-gallery `hgrid`
contract consumed by `pointed_metric_seed_of_restricted_gallery_pair`.  It
carries adjacent raw provenance explicitly, constructs a
`PointedCommonCenterGalleryPair`, and requires every gallery edge to be a
checked `PointedSeedEdge` from retained raw provenance, ordinary common-model
overlap, or the upstream flat real-Jost EOW transfer.

The already checked support remains useful but not sufficient by itself.  The
raw `(4.12)` seed-to-overlap metric ball is checked as
`BHW.OS45BHWJostHullData.OS412SeedWindow_initialSectorOverlap_metricBallChart`.
The neutral topology/SCV support lemmas are
`SCV.exists_open_connected_neighborhood_of_joinedIn_subset_open` and
`SCV.exists_metric_ball_differentiableOn_subset_of_mem_open`; endpoint and
overlap metric-ball shrinks use
`SCV.exists_metric_ball_subset_inter_of_mem_open`.

Lean-entry correction, 2026-05-17 after the "smallest statement" audit:
implementation must be milestone-driven, not support-lemma-driven.  The Stage-A
proof docs are now complete only in the following sense: Lean should enter the
direct producer and close the next named proof block end-to-end before looking
for reusable support.  A support theorem may be split out only when the current
milestone below exposes a concrete local obligation with no OS/QFT content.
The ordered milestones are:

1. build `OmegaOrd0/BOrd0`, `OmegaSeed412/BSeed412`, and the transported
   usable adjacent chart `OmegaAdj0/BAdj0` from the genuine raw `(4.12)` seed;
2. prove the ordinary and raw-adjacent fixed-test side-height selections
   `hOrd_fixed_psi0` and `hAdj_fixed_psi0`;
3. prove endpoint DCT and carrier-pairing normalizations, yielding
   `hOrd_boundary_to_source` and `hAdj_boundary_to_source`;
4. prove `hzero_plus` and `hzero_minus` for the local flat zero-height
   pairings by combining the two branch/source asymptotic transfers with the
   checked common source limit;
5. construct the overlap-centered adjacent comparison grid and consume it to
   obtain `Wadj`;
6. prove the ordinary overlap seed `Word`, the adjacent overlap seed `Wadj`,
   and the difference overlap equality by the checked SCV two-seed identity
   theorem;
7. glue the local differences with `SCV.glued_iUnion` to produce the actual
   `Ucx`, `Hdiff`, Wick zero pairing, and horizontal common-edge trace fields
   consumed by
   `BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ`.

Lean status, 2026-05-17 after the pointed-grid consumer port: the Hdiff
companion now checks the neutral finite pointed chain, endpoint retargeting,
two-gallery common-center consumer, retargeted-gallery seed composition, and
product-domain identity-theorem propagation from pointed seeds to full
metric-ball overlaps.  This does not prove `Wadj` by itself and is not a public
wrapper; it removes the generic topology/SCV part of milestones 5-6 from the
critical path.  The direct implementation block is now the actual OS45
`hgrid` edge seeds: retained raw `(4.12)` provenance, ordinary common-model
overlap, and the upstream flat real-Jost EOW open seed produced from the local
zero-height plus/minus pairing data.

Lean status, 2026-05-17 initial chart port: the same companion now also checks
private chart adapters for the ordinary `(4.1)` metric-ball window and the
genuine raw adjacent `(4.12)` seed window:
`OS45BHWJostHullData.ordinaryWick_pointedChartInWindow` and
`OS45BHWJostHullData.OS412SeedWindow_pointedChart`.  They merely put the already
checked OS-I local chart data into the private `PointedMetricBranchChart`
format used by the direct Hdiff proof; they do not replace the raw adjacent
seed by the downstream deterministic endpoint branch.

Lean status, 2026-05-17 edge-source port: the Hdiff companion now also checks
the local edge-source consumers for milestone 5.  Ordinary/common-model edges
are produced by `pointed_seed_edge_of_common_model`; retained raw `(4.12)`
edges survive endpoint retargeting by `pointed_seed_edge_retarget_both`; and the
flat real-Jost crossing edge is produced by
`flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM` from the
checked local zero-height EOW reducer plus the two chart-to-model equalities.
The earlier private source-representation bridge has been removed from the
Hdiff companion as wrapper-shaped indirection: the flat crossing consumes the
actual local zero-height pairings `hzero_plus`/`hzero_minus` and the local CLM
`Tlocal` directly.  The edge-source algebra is no longer a proof-doc gap; the
implementation proceeds by proving those zero-height pairings from the
side-height transfer transcript and then assembling the finite OS45 `hgrid`
with the checked edge sources.
The flat gallery orientation helper `PointedSeedEdge.symm` is now also checked
privately in the Hdiff companion; it only reverses an existing pointed seed and
adds no new analytic content.

Wrapper-removal correction, 2026-05-17: the previously checked private
`sourceRepresentsOn_of_flat_commonBoundary_zero` and
`flat_realJost_EOW_pointed_seed_of_sourceRepresentsOn` detours have been
deleted from the Hdiff companion.  They were coordinate-correct, but the
current upstream flat crossing does not need the full source-window
representation; it needs the local zero-height pairings already consumed by
`BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`.
The genuine content is therefore the flat compact-test zero supplied by the
ordinary and raw-adjacent branch/source asymptotic transfers plus the checked
source-side common limit, not an intermediate `hsource_zero_rep` wrapper.

Implementation audit correction, 2026-05-17: the coordinate/CLE and pointed
gallery consumers above are Lean-backed, but the proof-local names
`chainOrd`, `chainAdj`, `Word`, `Wadj`, `hOrd_fixed_psi0`, and
`hAdj_fixed_psi0` are not yet Lean objects.  They must not be introduced as a
record of assumptions.  The next proof-doc/Lean milestone is the genuine
one-branch OS-I producer inside the direct Hdiff proof: construct those objects
from the `(4.1)` ordinary seed and the raw `(4.12)` adjacent seed, then use the
checked side-height/source-side support to prove the fixed-test leaves.  A Lean
edit that assumes any of these fields has not entered the hard proof.

Pointed-gallery correction, 2026-05-17: milestone 5 must use the restricted
`hgrid` contract in `docs/theorem2_wadj_branch_law_transcript.md`.  The checked
consumer retargets both terminal charts to the actual observed overlap point
`z0`; the proof supplies a `PointedCommonCenterGalleryPair` for those
restrictions; every consecutive edge seed is open and contains the same `z0`.
Do not implement the older all-pair-gallery version that recursively
manufactures pair seeds.  The all-overlap SCV identity theorem is still used
later for final local-difference gluing, but not as the adjacent seed consumer.

Pointed-gallery local-case correction, 2026-05-17: the `hgrid` proof must not
hide the hard step behind abstract plan-list stand-ins.  At the observed
overlap point `z0`, perform the local OS-I case split and build the pair
literal directly:
ordinary-sector overlaps compare both restrictions to the local ordinary
`extendF` model; adjacent-sector overlaps retarget retained raw `(4.12)`
provenance to the same raw local chart; flat real-Jost overlaps use a
one-step/two-step gallery through the plus ordinary flat chart, with the
minus-to-plus edge supplied only after the proof-local zero-height plus/minus
pairings by `flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM`.
The needed symmetry of a `PointedSeedEdge` is a private local helper, not a
theorem wrapper.

Proof-doc status, 2026-05-17: the active companion transcript spells out
the flat zero-height pairing body down to the fixed-test scalar cancellation,
moving-test perturbation, endpoint DCT, ordinary/raw-adjacent side-height
transfers, and common source-side limit.  It also uses the checked private
`PointedMetricBranchChart`, `PointedSeedEdge`, and
`PointedCommonCenterGalleryPair` surfaces for the adjacent seed instead of the
older pseudo grid vocabulary.  The avoidable intermediate source-representation
and common-boundary packets have been removed from the active skeleton;
`AdjEdge = OrdEdge` is derived directly from `hzero_plus` and `hzero_minus`
against `Tlocal`.

The blocker identified by the implementation audit was narrower than the earlier
flat-transfer discussion: the transcript had to make the one-branch OS-I
producer fully explicit.  That producer is not a new public theorem surface and
not a bundled assumption record.  It is the in-body construction of the two
private chains:

```lean
-- Ordinary `(4.1)` incoming element.
let OmegaOrd0 : Set (Fin n -> Fin (d + 1) -> Complex) :=
  BHW.ExtendedTube d n ∩ H.ΩJ
let BOrd0 : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => BHW.extendF (bvt_F OS lgc n) z

-- Raw adjacent `(4.12)` incoming element.  This is upstream seed data.
let OmegaSeed412 : Set (Fin n -> Fin (d + 1) -> Complex) :=
  {z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ
let BSeed412 : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
```

The ordinary chain may compare local charts to `BOrd0` on
`BHW.ExtendedTube d n ∩ H.ΩJ`.  The adjacent chain must compare local charts to
`BSeed412` on `OmegaSeed412` until terminal transport has been proved; the
deterministic endpoint function
`fun z => BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) P.τ z)`
is an outgoing rewrite, not an incoming seed.  The live compact docs pass the
route scans for stale adjacent seeds, forbidden finite-chain wrappers, and
forbidden detour language.

Proof-doc progress, 2026-05-17: the companion Wadj transcript now spells out
the finite chain assembly along `gamma` as an in-body reachability proof.  For
each branch kind, `Reach kind t` means that a finite one-branch chain from the
actual initial germ to `gamma t` has already been constructed.  The local
OS-I transfer cases make `Reach kind` open, the same local symmetric transfer
makes its complement open, and `IsClopen.eq_univ` on `unitInterval` gives the
terminal chain.  This replaces the vague "choose a compact subdivision"
paragraph with Lean-facing pseudocode and still introduces no public chain,
`Wadj`, side-transfer, or Hdiff wrapper.

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
producer of `hzero_plus`/`hzero_minus` and they do not identify the flat
zero-height pairing with a Schwinger or Wick anchor by themselves.

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
`(4.14)` local zero-height pairings at the flat crossing to obtain
`hadj412_common_trace` via the checked local zero-height EOW reducer.  Only
after the genuine `(4.12)` element has both Wick and common-edge traces should
the proof use
`BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3` with `Badj412` as the adjacent
branch to obtain `h45_source_eqOn`; that downstream equality then feeds the
checked source-common-edge flat bridge.  The upstream flat crossing itself
uses `hzero_plus`/`hzero_minus` and the checked local zero-height reducer, not
a source-representation or public common-boundary packet.  The deterministic branch
`z ↦ extendF (bvt_F OS lgc n) (permAct P.τ z)` may appear only in
`hadj412_common_trace`, after the raw seed has been transported to the
endpoint-centered chart.  Adding a public theorem that merely assumes this
transfer, `Wadj`, or `Hdiff` is wrapper churn.

The tempting initial-overlap shortcut was first rejected in a non-certifying
raw-model sanity check and is now treated as certified only by the pinned
Deep Research Max route documented in the harness and `agents_chat.md`.
The rejected shortcut is
`Fadj z := extendF (bvt_F OS lgc n) (permAct P.τ z)`.  For the strict route,
that definition is downstream endpoint identification, not upstream adjacent
branch data.  The live implementation must therefore continue to construct
`Badj412` from the raw `(4.12)` seed, prove the OS-I `(4.14)` flat boundary
transfer, transport equality through the finite Figure-2-4 gallery, and only
after that rewrite the endpoint as the deterministic permuted branch.

Proof-doc correction after the compact-test audit: before editing any local
Lean file, the proof transcript must expose the direct boundary-limit theorem
used in `hhorizontal_zero`.  Do **not** implement the earlier finite-height
`chiWick` helper; the completed compact-test audit rejects that theorem shape.
Ordinary distributional analytic continuation gives side-height limits, not a
literal compactly supported Wick-side replacement test.

The pure moving-test/Banach-Steinhaus principle is no longer a live theorem-2
blocker: `SCV.tube_boundaryValueData_moving_of_fixed` proves the moving-test
upgrade for an already-selected tube boundary functional,
`bvt_boundary_values_moving` specializes it to the selected OS witness
`bvt_F/bvt_W`, and the OS45 compact flat-chart tests use a direct
compact-support perturbation estimate after fixed-test convergence.  The remaining
mathematical gap is narrower and sharper: prove
the OS-I branch/source asymptotic transfers for the ordinary `(4.1)` and
transported raw adjacent `(4.12)` side-height families, then combine them with
the checked source-side Schwinger common limit and checked side-limit algebra
to obtain `AdjEdge = OrdEdge`.  Individual zero-height-to-Schwinger
normalizations are not the primitive Stage-A target.

Active Stage-A contract, not a closure declaration: the active Wadj transcript now expands the
coordinate and moving-test layers down to local `have`s and separates boundary
selection from source normalization.  The fixed-test leaves

```lean
hOrd_fixed_psi0
hAdj_fixed_psi0
```

These are not wrapper names.  They are proof-local obligations inside
`hPlus_asymptotic_eta0` and `hMinus_asymptotic_eta0`.  Their job is only to
select the boundary functional from the current one-branch analytic element
and prove fixed-test side-height convergence on the correct sheet for the
concrete compact source test
`psi0 = D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi`.  The all-Schwartz
fixed-test theorem remains upstream on the raw tube boundary data; after the
local `sourceSide` pullback the transcript must not claim compact support or
cutoff inversion for an arbitrary `SchwartzNPoint`.  For the ordinary side the
incoming sheet is `BHW.ExtendedTube d n`; for the raw-adjacent side it is the
transported `(4.12)` seed window
`{z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ`.
The adjacent endpoint formula `extendF (bvt_F OS lgc n) (BHW.permAct P.τ z)`
may be used only after this raw analytic element has reached the terminal
endpoint chart.

Lean progress, 2026-05-17: the first fixed-test and moving-test
boundary-value inputs are now checked privately in the Hdiff companion, not
assumed by a public wrapper.
`ordinary41_fixed_test_boundaryValue_extendF` proves the ordinary `(4.1)`
`extendF` ray by rewriting to `bvt_F` on the positive forward tube and applying
`bvt_boundary_values`.  `raw412_fixed_test_boundaryValue` proves the raw
`(4.12)` fixed ray from `bvt_boundary_values` after the source-label change of
variables and `BHW.permuteSchwartz`.  Their moving-test companions
`ordinary41_moving_boundaryValue_extendF` and `raw412_moving_boundaryValue`
upgrade the same two selected OS-I rays to filters of source tests; the raw
adjacent moving leaf again changes variables before the boundary-value theorem
and only then rewrites the endpoint by `BHW.permuteSchwartz`.  The remaining
work is the source-side quarter-turn transfer: these checked raw leaves may be
used only after the proof has produced the exact half-time raw ray and cone
hypotheses.  They do not by themselves replace the source-side
side-height/source asymptotic blocks.

The genuine OS-I branch/source transfer is now exposed by two local
boundary-to-source leaves:

```lean
hOrd_boundary_to_source :
  Word ((psi0).1 : SchwartzNPoint d n) =
    ∫ u, bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
      (((psi0).1 : SchwartzNPoint d n) u)

hAdj_boundary_to_source :
  Wadj ((psi0).1 : SchwartzNPoint d n) =
    ∫ u, bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
      (((psi0).1 : SchwartzNPoint d n) u)
```

Each leaf is a uniqueness-of-limits calculation, not a new exported theorem.
The selected fixed-test limit (`hOrd_fixed_psi0` or `hAdj_fixed_psi0`) gives the CLM
value.  A second endpoint-continuity limit computes the same side-height
integral at `eps = 0`, using terminal-sheet holomorphic continuity, the
checked compact SourceSide collar and finite branch bound, compact support of
`psi0`, the checked zero-extension measurability helper, and
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.  The
zero-height endpoint is then rewritten in two stages.  First the terminal
branch equality gives the pairing against the `bvt_F` value on the
quarter-turned common-edge carrier.  Then the local OS-I `(4.14)` pairing
normalization identifies that carrier pairing with the Wick source pairing.
On the ordinary side the carrier is
`BHW.os45QuarterTurnConfig (fun k => wickRotatePoint (u k))`; on the
raw-adjacent side, after retained `(4.12)` terminal transport and `permAct`,
the carrier is
`BHW.os45QuarterTurnConfig (fun k => wickRotatePoint (u (P.τ k)))`.  Neither
carrier is literally the unturned Wick point, so this step must not be replaced
by a pointwise coordinate `simp` or pointwise `bvt_F` equality.

The DCT subproof is now Lean-script shaped in the companion transcript.  For
each side it supplies:

```lean
hpsi0_compact
hpsi0_support_V
h*_endpoint_mem
h*_eventual_collar
h*_pointwise
h*_bound
h*_aestrongly
```

and then calls
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence (bound := g)`.
The support facts are honest local ingredients, not wrappers.  The compact
side-tube collar/majorant, pointwise branch convergence, closed-support
zero-extension AEStronglyMeasurable step, fixed-height source continuity, and
the full endpoint dominated-convergence assembly are now checked SourceSide
support inputs:
`BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps` and
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport`.
The remaining endpoint normal form is the flat-boundary pairing cancellation
script.  The collar proof is concrete: compactness of
`tsupport psi0`, openness of the terminal carrier, and continuity of
`sourceSide` give `δ > 0` with
`{sourceSide sgn eps eta0 u | eps ∈ Icc 0 δ, u ∈ tsupport psi0}` inside the
carrier; continuity then gives a finite bound `M`, so the DCT majorant is
`M * ‖psi0 u‖`.  The normal form splits into a coordinate carrier identity and
a local OS-I `(4.14)` pairing identity.  Neither may assume the asymptotic
transfer, `AdjEdge = OrdEdge`, `Hdiff`, `Wadj`, the downstream deterministic
adjacent branch, or a common-boundary CLM.

Lean support target for the collar leaf, before any branch or boundary-value
argument, is the following direct compactness lemma:

```lean
theorem eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    {U : Set (Fin n -> Fin (d + 1) -> ℂ)}
    (hU_open : IsOpen U)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U) :
    ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈ U
```

Proof script: apply `BHW.continuous_os45FlatCommonChartSourceSide` to obtain
`∀ u ∈ K, ∀ᶠ p in 𝓝 ((0 : ℝ), u), sourceSide p.1 p.2 ∈ U`; feed this into
`hK.eventually_forall_of_forall_eventually` and then restrict from `𝓝 0` to
`𝓝[Set.Ioi 0] 0` by `nhdsWithin_le_nhds`.  In the endpoint DCT proof, instantiate
`K := tsupport psi0` and `U := chain*.terminalCarrier`.  This discharges only
`h*_eventual_collar`; the checked finite-bound lemma below discharges the
compact-collar branch estimate, and DCT still separately assembles
measurability, integrability, domination, and pointwise convergence.

The finite branch-bound support target is likewise a compactness statement, not
a branch-transfer theorem:

```lean
theorem exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    {U : Set (Fin n -> Fin (d + 1) -> ℂ)}
    (hU_open : IsOpen U)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U)
    {F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
    (hF_cont : ContinuousOn F U) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ K,
          ‖F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u)‖ ≤ M
```

Proof script: extract `r > 0` from the full-neighborhood compact-collar proof,
take `δ := r / 2`, form the compact image of `Set.Icc 0 δ ×ˢ K` under
`sourceSide`, prove this image is contained in `U`, and apply
`IsCompact.exists_bound_of_continuousOn` to `F`.  The resulting `M` bounds the
terminal branch uniformly for all sufficiently small positive `eps`.  The DCT
majorant is then `fun u => M * ‖psi0 u‖`, with the off-support case supplied by
`image_eq_zero_of_notMem_tsupport`.

Pointwise convergence of the terminal branch is the corresponding singleton
version:

```lean
theorem tendsto_comp_os45FlatCommonChartSourceSide_nhdsWithin
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n)
    {U : Set (Fin n -> Fin (d + 1) -> ℂ)}
    (hU_open : IsOpen U)
    {F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
    (hF_cont : ContinuousOn F U)
    (h0 :
      BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U) :
    Tendsto
      (fun eps : ℝ =>
        F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u))
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (F (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u)))
```

In `h*_pointwise`, use this theorem on support and multiply by the fixed test
value; off support, rewrite the test value to zero by
`image_eq_zero_of_notMem_tsupport`.

Lean-entry contracts for those proof-local leaves:

```lean
-- Analytic estimate leaf, ordinary side.  May be a private support lemma only
-- if it proves this exact compact-collar DCT statement: endpoint support in
-- `chainOrd.terminalCarrier`, uniform small-`eps` collar inside that carrier,
-- finite branch bound on the collar, majorant `M * ‖psi0 u‖`, pointwise
-- convergence by `BHW.tendsto_comp_os45FlatCommonChartSourceSide_nhdsWithin`,
-- and AEStronglyMeasurability by the private zero-extension support helper
-- `BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport`.
have hOrd_endpoint_DCT :
  Tendsto
    (fun eps =>
      ∫ u : NPointDomain d n,
        chainOrd.terminalBranch (sourceSide (1 : Real) eps eta0 u) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u))
    l
    (nhds
      (∫ u : NPointDomain d n,
        chainOrd.terminalBranch (sourceSide (1 : Real) 0 eta0 u) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u)))

-- Analytic estimate leaf, raw-adjacent side.  Same compact-collar DCT proof,
-- but on the terminal carrier transported from the genuine `(4.12)` seed.
have hAdj_endpoint_DCT :
  Tendsto
    (fun eps =>
      ∫ u : NPointDomain d n,
        chainAdj.terminalBranch (sourceSide (-1 : Real) eps eta0 u) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u))
    l
    (nhds
      (∫ u : NPointDomain d n,
        chainAdj.terminalBranch (sourceSide (-1 : Real) 0 eta0 u) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u)))

-- OS-I pairing-normalization leaf, ordinary side.  The preceding coordinate
-- proof rewrites the endpoint branch to the quarter-turned carrier.  The full
-- local script in `theorem2_wadj_branch_law_transcript.md` introduces
-- `e`, `J`, `psi0Flat`, the plain CLE pullback
-- `pullFlatToSource := SchwartzMap.compCLMOfContinuousLinearEquiv Complex e`,
-- `carrierPairing`, and `wickPairing`, defines
-- `WordFlat := J • (Word.comp pullFlatToSource)`, proves
-- `pullFlatToSource psi0Flat = psi0`, then proves
-- `WordFlat psi0Flat = J * carrierPairing` from endpoint uniqueness/DCT and
-- `WordFlat psi0Flat = J * wickPairing` from the ordinary Wick trace before
-- cancelling nonzero `J`.
have hOrd_carrier_pairing :
  (∫ u : NPointDomain d n,
      bvt_F OS lgc n
        (BHW.os45QuarterTurnConfig (fun k => wickRotatePoint (u k))) *
      ((((psi0).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex) u)) =
  ∫ u : NPointDomain d n,
      bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
      ((((psi0).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex) u)

-- OS-I pairing-normalization leaf, raw-adjacent side.  Define the same
-- plain CLE pullback and
-- `WadjFlat := J • (Wadj.comp pullFlatToSource)` locally; the full script
-- introduces `carrierAdjPairing` and `wickAdjPairing`, proves
-- `pullFlatToSource psi0Flat = psi0`, proves
-- `WadjFlat psi0Flat = J * carrierAdjPairing` by endpoint uniqueness/DCT and
-- raw `(4.12)` terminal provenance, proves
-- `WadjFlat psi0Flat = J * wickAdjPairing` from the transported raw-adjacent
-- Wick trace, then cancels nonzero `J`.  Do not use the downstream
-- deterministic adjacent branch.
have hAdj_carrier_pairing :
  (∫ u : NPointDomain d n,
      bvt_F OS lgc n
        (BHW.os45QuarterTurnConfig
          (fun k => wickRotatePoint (u (P.τ k)))) *
      ((((psi0).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex) u)) =
  ∫ u : NPointDomain d n,
      bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
      ((((psi0).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex) u)
```

After those two OS-I `(4.14)` leaves are proved, the normalization steps are
checked algebra: ordinary uses
`bvt_euclidean_restriction (d := d) OS lgc n (D.toZeroDiagonalCLM 1 phi)`;
raw-adjacent uses
`BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger`.

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

Do not introduce a public wrapper helper for the zero conclusion.  The zero
conclusion must be proved in the body of the upstream `hadj412` flat real-Jost
crossing for the current compact source/flat test.  A small support lemma is
allowed only if the current milestone above has already reduced to a genuine
neutral local ingredient such as endpoint continuity/dominated convergence for
the terminal branch on the compact side-tube collar, or the zero-height endpoint
carrier/pairing normal form.  Factoring out a theorem before the relevant
milestone has exposed that local ingredient is wrapper churn
when the theorem assumes either asymptotic transfer, `AdjEdge = OrdEdge`,
`Hdiff`, `Wadj`, or a common-boundary CLM.

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

Both transfers must be proved from the same four local ingredients:

1. side-window membership from
   `BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24`, giving the
   ordinary plus and selected adjacent minus sheet domains for all small
   positive heights and all `eta in Keta`;
2. the checked branch integral pullback
   `BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest`
   for fixed source tests, plus the side-zero-diagonal CLM pullback and
   `D.toSideZeroDiagonalCLM_apply`/support removal for the moving cutoff tests;
   these identify the exact flat CLE, Jacobian, and translated-test
   cancellation without selecting a boundary value;
3. the OS-I `(4.14)` Fourier-Laplace covariance/boundary-value theorem,
   applied to the ordinary `(4.1)` analytic element and to the transported raw
   adjacent `(4.12)` analytic element, with the existing moving-test upgrade
   only after the correct boundary functional has been selected;
4. endpoint-limit uniqueness: the selected CLM limit is compared with an
   independent endpoint-continuity/DCT limit at `eps = 0`, then the endpoint
   is rewritten first to the quarter-turned carrier and only then, by local
   OS-I `(4.14)` pairing normalization, to the ordinary or raw-adjacent
   Wick/source pairing.

The checked source-side Schwinger limits and
`SCV.eq_zeroHeight_of_common_sideLimit` are downstream algebra.  They are not
allowed to serve as substitutes for either `(4.14)` branch/source transfer.

Fixed-test guard: the OS45 `sourceSide` path should not be rewritten to a
nonexistent plain forward-cone direction.  Ordinary fixed-test selection is the
OS-I boundary-value/covariance statement for
`BHW.os45FlatCommonChartSourceSide` on incoming sheet `BHW.ExtendedTube d n`
and outgoing flat sheet `BHW.os45FlatCommonChartOmega d n 1`.  Raw-adjacent
fixed-test selection starts from the retained
`OmegaSeed412/BSeed412` preimage-forward-tube window and reaches
`BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)` only through the adjacent
one-branch chain; `extendF o permAct` appears only after terminal transport.

The proof-local fixed-test leaves are therefore compact source-test
specializations:

```lean
have hOrd_fixed_psi0 :
  Tendsto
    (fun eps =>
      ∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (sourceSide (1 : Real) eps eta0 u) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u))
    l
    (nhds (Word ((psi0).1 : SchwartzNPoint d n)))

have hAdj_fixed_psi0 :
  Tendsto
    (fun eps =>
      ∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ
            (sourceSide (-1 : Real) eps eta0 u)) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u))
    l
    (nhds (Wadj ((psi0).1 : SchwartzNPoint d n)))
```

`hOrd_fixed_psi0` is selected from the ordinary `(4.1)` chain plus `(4.14)`
covariance on the checked `sourceSide` normal form.  `hAdj_fixed_psi0` is
selected from the raw `(4.12)` seed after applying `permAct P.τ`, then
transported through the retained adjacent one-branch chain.  These leaves are
the live mathematical proof bodies; support lemmas may only feed their sheet
membership, carrier equality, or moving-test hypotheses.

The implementation-level proof of these leaves is now the compact `psi0`
flat-chart scalar-cancellation argument, not a new wrapper theorem.  The
all-Schwartz fixed-test theorem is used only on the raw tube boundary data
before this local source pullback.  For the ordinary `sourceSide` leaf, set

```lean
let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n
let pullFlatToSource :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
let psi0Flat :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm)
    ((psi0).1 : SchwartzNPoint d n)
let psiFlat_eps (eps : Real) :=
  SCV.translateSchwartz (-(eps • eta0)) psi0Flat
```

The chosen side-height direction is a flattened EOW direction only.  Do not
manufacture raw OS-I cone hypotheses from this vector.  The retired candidate
`InForwardCone d n (BHW.unflattenCfgReal n d eta0)` together with the
signed/permuted condition for `-BHW.unflattenCfgReal n d eta0` is
cone-inconsistent in the ordinary forward cone.  The raw Hdiff leaves
`ordinary41_moving_boundaryValue_extendF` and `raw412_moving_boundaryValue`
are available only after the source-side quarter-turn geometry has produced an
actual raw tube ray with
`BHW.os45HalfTimeDirection (d := d) (n := n) σ x`, using
`BHW.os45HalfTimeDirection_mem_forwardCone_of_ordered` and, on the adjacent
side, `BHW.os45HalfTimeDirection_adjacent_swap_eq` plus the retained raw
`(4.12)` provenance.

The fixed-test flat/source transfer therefore starts with the checked
source-side coordinate identity
`BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest`.
Use it with `σ = 1`, `ρperm = 1`, `sgn = 1`, `η = eta0`, and
`ψFlat = psi0Flat` on the ordinary side, and with
`σ = P.τ.symm * 1`, `ρperm = 1`, `sgn = -1`, `η = eta0`, and the same
`ψFlat` on the adjacent side.  The theorem is the checked form where the
translated flat test cancels the real side shift, so the right-hand source
test is the fixed pullback `psi0Flat (e u) = psi0 u`.  The `hg_shift`
hypothesis comes from the checked compact-support side integrability package
applied to `psi0Flat`, not to the original `phi`:

```lean
obtain ⟨hpsi0Flat_compact, hpsi0Flat_edge⟩ :
    HasCompactSupport
        (psi0Flat : BHW.OS45FlatCommonChartReal d n -> Complex) ∧
      tsupport
        (psi0Flat : BHW.OS45FlatCommonChartReal d n -> Complex) <=
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) := by
  simpa [psi0, psi0Flat, e] using
    D.toZeroDiagonalCLM_flatPullback_support
      (1 : Equiv.Perm (Fin n)) phi hphiUsource
      (hUsource_sub_Ksource.trans hKsource_sub_P)

have hpsi0Flat_integ :=
  BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
    (d := d) hd OS lgc (P := P) Keta hKeta hKetaC
    psi0Flat hpsi0Flat_compact hpsi0Flat_edge
```

The ordinary `hpullOrd` uses `(hpsi0Flat_integ eps eta0 hKeta_eta0).1`; the
raw-adjacent `hpullAdj` uses the `.2` component.  The selected fixed
source-side limits are the genuine local OS-I transfer obligations.  They are
not wrapper assumptions and they are not obtained by unflattening `eta0`.
Prove them in place by first selecting the matching flat translated-test
boundary value from the retained one-branch OS-I trace, then applying the
checked source-side translated-test/Jacobian cancellation theorem:

```lean
let FOrd : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  BHW.extendF (bvt_F OS lgc n)
let FAdj : (Fin n -> Fin (d + 1) -> Complex) -> Complex := fun z =>
  BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) P.τ z)

have hOrd_sourceSide_fixed :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          FOrd (BHW.os45FlatCommonChartSourceSide
            d n (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta0 u) *
          ((psi0).1 : SchwartzNPoint d n) u)
      l
      (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
  -- Use `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff` for
  -- source-side sheet membership.  The flat boundary selector is produced by
  -- the ordinary one-branch terminal trace, and
  -- `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest`
  -- turns that selected flat limit into the displayed source-side limit.
  -- The endpoint/source normalization is a separate uniqueness-of-limits
  -- calculation below.

have hAdj_sourceSide_fixed :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          FAdj (BHW.os45FlatCommonChartSourceSide
            d n (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta0 u) *
          ((psi0).1 : SchwartzNPoint d n) u)
      l
      (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
  -- Use the same source-side sheet and scalar-cancellation calculation with
  -- `FAdj`.  The adjacent raw `(4.12)` element must be transported through
  -- `chainAdj` to select the flat minus boundary value before this leaf lands
  -- in `Wadj psi0`; the endpoint `extendF o permAct` expression is downstream
  -- bookkeeping, not seed data.
```

The matching flat boundary selectors are not assumptions.  The companion Wadj
transcript expands them as finite inductions over the private one-branch
chains: base OS-I boundary datum, equality on each pointed overlap at one
lifted side point, compact-support collar control for that side point,
uniqueness of limits across each edge, and terminal identification with
`WordFlat` or `WadjFlat`.  A helper is allowed only for this neutral
compact-collar or finite-chain induction over explicit pointed seed edges.
The collar proof is written out there from `tsupport psi0Flat` compactness,
continuity of the lifted side path, and
`SCV.mem_support_translateSchwartz_iff`; no public boundary-value selector is
being assumed.
The transcript also separates the terminal normal form: the chain induction
lands in the terminal branch evaluated at `sideLift`, then the terminal model
field rewrites this integral to `FlatOrd` or `FlatAdj` on the same collar before
the checked scalar-cancellation theorem is applied.

If a raw moving leaf is used inside either source-side proof, first prove the
exact quarter-turn identity that rewrites the relevant `sourceSide` path to a
raw ray with `BHW.os45HalfTimeDirection`; then discharge the cone condition
with `BHW.os45HalfTimeDirection_mem_forwardCone_of_ordered` or the adjacent
swap version.  Without that identity, the raw Hdiff leaves are not applicable.

The source-side fixed leaf should enter Lean in this concrete order.  This is
the hard producer body, not a theorem wrapper:

```lean
let sourceSide (sgn : Real) (eps : Real)
    (eta : BHW.OS45FlatCommonChartReal d n) (u : NPointDomain d n) :=
  BHW.os45FlatCommonChartSourceSide
    d n (1 : Equiv.Perm (Fin n)) sgn eps eta u

have hOrd_endpoint_mem_on_Ksource :
    forall u in Ksource,
      sourceSide (1 : Real) 0 eta0 u ∈ chainOrd.terminalCarrier := by
  -- rewrite by `BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge`;
  -- use the ordinary terminal chart-in-window field for the common-edge point.

have hOrd_endpoint_DCT :
    Tendsto
      (fun eps : Real =>
        integral fun u : NPointDomain d n =>
          chainOrd.terminalBranch (sourceSide (1 : Real) eps eta0 u) *
          (((psi0).1 : SchwartzNPoint d n) u))
      l
      (nhds
        (integral fun u : NPointDomain d n =>
          chainOrd.terminalBranch (sourceSide (1 : Real) 0 eta0 u) *
          (((psi0).1 : SchwartzNPoint d n) u))) := by
  exact
    BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
      (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (1 : Real))
      (η := eta0) chainOrd.terminalCarrier_open
      chainOrd.terminalBranch_continuousOn
      hpsi0_compact ((psi0).1 : SchwartzNPoint d n).continuous
      hOrd_endpoint_mem_on_Ksource

have hOrd_fixed_psi0 :
    Tendsto
      (fun eps : Real =>
        integral fun u : NPointDomain d n =>
          chainOrd.terminalBranch (sourceSide (1 : Real) eps eta0 u) *
          (((psi0).1 : SchwartzNPoint d n) u))
      l
      (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
  -- Rewrite the terminal branch to `FOrd` on the eventual source-side collar
  -- with `chainOrd.terminal_eq_ordinary_global`, kill the complement of
  -- `Ksource` by compact support of `psi0`, and apply the selected ordinary
  -- source-side leaf above.

have hOrd_endpoint_as_source :
    (integral fun u : NPointDomain d n =>
      chainOrd.terminalBranch (sourceSide (1 : Real) 0 eta0 u) *
      (((psi0).1 : SchwartzNPoint d n) u)) =
    (integral fun u : NPointDomain d n =>
      bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
      (((psi0).1 : SchwartzNPoint d n) u)) := by
  -- pointwise: rewrite the zero sourceSide by
  -- `BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge`, use the ordinary
  -- terminal trace on `tsupport psi0`, and normalize the quarter-turned
  -- carrier by the ordinary `(4.14)` pairing equality.

have hOrd_boundary_to_source :
    Word ((psi0).1 : SchwartzNPoint d n) =
      integral fun u : NPointDomain d n =>
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
        (((psi0).1 : SchwartzNPoint d n) u) := by
  have hWord_endpoint :
      Word ((psi0).1 : SchwartzNPoint d n) =
        integral fun u : NPointDomain d n =>
          chainOrd.terminalBranch (sourceSide (1 : Real) 0 eta0 u) *
          (((psi0).1 : SchwartzNPoint d n) u) := by
    exact tendsto_nhds_unique hOrd_fixed_psi0 hOrd_endpoint_DCT
  exact hWord_endpoint.trans hOrd_endpoint_as_source

have hOrd_source_norm :
    Word ((psi0).1 : SchwartzNPoint d n) =
      OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi) := by
  -- Rewrite `hOrd_boundary_to_source` by `psi0 =
  -- D.toZeroDiagonalCLM 1 phi` and the checked Euclidean restriction.

have hAdj_endpoint_mem_on_Ksource :
    forall u in Ksource,
      sourceSide (-1 : Real) 0 eta0 u ∈ chainAdj.terminalCarrier := by
  -- rewrite by `BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge`;
  -- apply the adjacent terminal chart-in-window field after raw `(4.12)`
  -- transport has reached `chainAdj.terminalCarrier`.

have hAdj_endpoint_DCT :
    Tendsto
      (fun eps : Real =>
        integral fun u : NPointDomain d n =>
          chainAdj.terminalBranch (sourceSide (-1 : Real) eps eta0 u) *
          (((psi0).1 : SchwartzNPoint d n) u))
      l
      (nhds
        (integral fun u : NPointDomain d n =>
          chainAdj.terminalBranch (sourceSide (-1 : Real) 0 eta0 u) *
          (((psi0).1 : SchwartzNPoint d n) u))) := by
  exact
    BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
      (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (-1 : Real))
      (η := eta0) chainAdj.terminalCarrier_open
      chainAdj.terminalBranch_continuousOn
      hpsi0_compact ((psi0).1 : SchwartzNPoint d n).continuous
      hAdj_endpoint_mem_on_Ksource

have hAdj_fixed_psi0 :
    Tendsto
      (fun eps : Real =>
        integral fun u : NPointDomain d n =>
          chainAdj.terminalBranch (sourceSide (-1 : Real) eps eta0 u) *
          (((psi0).1 : SchwartzNPoint d n) u))
      l
      (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
  -- Rewrite the terminal branch to `FAdj` on the eventual source-side collar
  -- with the retained raw `(4.12)` terminal formula transported by `chainAdj`,
  -- kill the complement of `Ksource`, and apply the selected adjacent
  -- source-side leaf above.

have hAdj_endpoint_as_source :
    (integral fun u : NPointDomain d n =>
      chainAdj.terminalBranch (sourceSide (-1 : Real) 0 eta0 u) *
      (((psi0).1 : SchwartzNPoint d n) u)) =
    (integral fun u : NPointDomain d n =>
      bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
      (((psi0).1 : SchwartzNPoint d n) u)) := by
  -- pointwise: use `chainAdj.terminal_eq_transported_adjacent_endpoint`,
  -- `BHW.permAct_os45FlatCommonChartSourceSide_zero`, and the retained raw
  -- `(4.12)` terminal trace.  The deterministic `extendF o permAct` formula
  -- appears only after this transport equality.

have hAdj_boundary_to_source :
    Wadj ((psi0).1 : SchwartzNPoint d n) =
      integral fun u : NPointDomain d n =>
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
        (((psi0).1 : SchwartzNPoint d n) u) := by
  have hWadj_endpoint :
      Wadj ((psi0).1 : SchwartzNPoint d n) =
        integral fun u : NPointDomain d n =>
          chainAdj.terminalBranch (sourceSide (-1 : Real) 0 eta0 u) *
          (((psi0).1 : SchwartzNPoint d n) u) := by
    exact tendsto_nhds_unique hAdj_fixed_psi0 hAdj_endpoint_DCT
  exact hWadj_endpoint.trans hAdj_endpoint_as_source

have hAdj_source_norm :
    Wadj ((psi0).1 : SchwartzNPoint d n) =
      OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi) := by
  -- Rewrite `hAdj_boundary_to_source` by the checked adjacent Wick/source
  -- normalization
  -- `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger`.
```

The moving-test upgrade then calls
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport`
with `φseq := fun eps => ((psiPlus eps eta0).1 : SchwartzNPoint d n)` or
`φseq := fun eps => ((psiMinus eps eta0).1 : SchwartzNPoint d n)`, the common
compact support supplied by
`D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually`, and the
zeroth-seminorm convergence supplied by
`D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero`.

The later source-side moving-test upgrade from fixed `psi0` to the
Figure-2-4 tests uses the checked support input
`BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually`
to put the moving plus test and the fixed source test in one compact source
carrier.  Invoke this checked support input with the original flat test `phi`
that defines `psiPlus/psiMinus`, the proof-local source packet
`Usource ⊆ Ksource`, and
`hphiUsource : tsupport phi ⊆
  (BHW.os45CommonEdgeFlatCLE d n 1) '' Usource`; do not feed it the auxiliary
flat pullback test `psi0Flat` from the scalar-cancellation
subleaf.  The checked seminorm input
`BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero`
supplies the zeroth Schwartz seminorm convergence; the local side-window theorem
and branch continuity give a uniform branch bound on the compact side collar;
and the difference integral is bounded by `M * volume(K) * supNorm`.  The
fixed source-side scalar cancellation is now checked as
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest`.
Call it only after the matching flat translated-test boundary limit has been
selected by the ordinary or raw-adjacent one-branch OS-I trace.  It removes the
common Jacobian from the exact translated-test pullback and produces the
source-side fixed limit; it does not select the flat boundary value and does
not replace the proof-local `(4.14)` trace.

The source-side fixed-to-moving step consuming the side-test inputs is the
assembled theorem
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport`
with the selected fixed leaf (`hOrd_fixed_psi0` or `hAdj_fixed_psi0`) as its
input limit.  Its proof expands through
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport`.

The retained raw `(4.12)` germ `OmegaSeed412/BSeed412` is used to select the
boundary CLM and later to prove the Wick-trace identity
`Wadj psi0 = wickAdjPairing`, not to introduce a chain-level flat-boundary
wrapper.  The minus-side sheet membership comes from the raw `(4.12)` window
plus `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`; the endpoint
`extendF o permAct` is not seed data.  No public adjacent side-transfer wrapper
is introduced.

Fixed-test implementation contract, corrected 2026-05-17: implement the
ordinary and raw-adjacent fixed-test leaves as source-side quarter-turn
selection scripts, not as exported transfer theorems.  In both cases:

```lean
-- local data only
let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n
have hJ_ne : J ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))

-- 1. `hpull*`: checked translated-test coordinate theorem gives
--      Flat*(eps) = J * SourceSide*(eps).
-- 2. `hsourceSide*_fixed`: prove the fixed source-side limit with
--      `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`,
--      `BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge`,
--      `BHW.permAct_os45FlatCommonChartSourceSide_zero` on the adjacent side,
--      and the compact-collar DCT theorem.
-- 3. Endpoint normalization: ordinary uses the `(4.1)/(4.14)` endpoint trace;
--      adjacent first transports `OmegaSeed412/BSeed412` through `chainAdj`,
--      then rewrites the terminal endpoint to the retained raw `(4.12)` Wick
--      trace.
-- 4. Moving-test upgrade: apply the checked common-compact-support theorem to
--      pass from fixed `psi0` to the actual side cutoff tests.
-- 5. Raw Hdiff moving leaves are optional inner substeps only after an exact
--      quarter-turn/half-time ray identity has been proved; they are never
--      called by unflattening or negating the flat EOW direction `eta0`.
```

The adjacent script must keep `OmegaSeed412/BSeed412` as the incoming analytic
element until `chainAdj` reaches the terminal chart.  The equality
`fun z => extendF (bvt_F OS lgc n) (BHW.permAct P.τ z)` is an endpoint rewrite
after raw transport, not the upstream seed.

Deep Research interaction
`v1_ChZwSjBJYXRhMkNKT0V4TjhQbUx2MkVBEhZwSjBJYXRhMkNKT0V4TjhQbUx2MkVB`
completed on 2026-05-16 and agrees with this theorem shape: keep
`sourceSide` as the actual OS45/BHW covariance path, do not replace it by a
plain forward-cone direction, and make support/domain and moving-test bounds
explicit before any distributional conclusion.  No new subtype/wrapper surface
is introduced from that advice; the guard is proof-local.

Proof-doc status, 2026-05-16: the companion Wadj transcript is now the
implementation source of truth for the fixed-test `sourceSide` selection, the
compact-collar endpoint DCT, and the endpoint carrier-pairing cancellation.  It
names the exact proof-local projections and private support helper needed by
Lean.  When Lean work resumes or continues, implement these proof-local
ingredients directly in the strict OS45 Hdiff companion and do not introduce
public wrappers for the side transfer, `AdjEdge = OrdEdge`, `Wadj`, `Hdiff`,
or the common-boundary CLM.

Lean support now checked in
`OSToWightmanLocalityOS45SourceSide.lean`: the no-cutoff source-side pullback
lemmas, the zero-height endpoint carrier identities
`BHW.os45FlatCommonChartSourceSide_zero` /
`BHW.permAct_os45FlatCommonChartSourceSide_zero`, the common-edge inverse
quarter-turn identities
`BHW.os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick`,
`BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge`, and
`BHW.permAct_os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick`, and
`BHW.continuous_os45FlatCommonChartSourceSide`.  The compact-collar DCT support
now also has checked topology/estimate lemmas
`BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact` and
`BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide`,
the pointwise branch-continuity lemma
`BHW.tendsto_comp_os45FlatCommonChartSourceSide_nhdsWithin`, and the
closed-support measurability helper
`BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport`.  The fixed-height
continuity helper
`BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps` and the full compact
support DCT assembly
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport`
are now checked as well.  These directly support the fixed-test source-side
calculation and discharge the DCT collar/majorant, pointwise-limit,
measurability, and integrability setup.  The compact-support moving-test error
estimate
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport`
and the assembled moving-test convergence theorem
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport`
are now checked too.  Their concrete side-test hypotheses are no longer informal:
`BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually`
gives eventual common compact support for the actual plus/minus source tests,
using the original flat test `phi` and the local source support
`hphiUsource`, and
`BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero`
gives the zeroth-seminorm convergence from the checked Schwartz convergence.
The assembled theorem packages fixed endpoint DCT, compact-support
perturbation, and the integral split for an arbitrary terminal branch
continuous on an open carrier; it still assumes the fixed endpoint limit has
already been selected.
`OSToWightmanLocalityOS45SourceSideMoving.lean` now also checks
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest`,
the fixed-test scalar-cancellation support theorem used immediately after
`hflatOrd`/`hflatAdj`; it is not a boundary-selection theorem and it does not
identify the moving side tests.
The Lean work is direct implementation of the OS-I fixed-test selection and the
flat-boundary comparison fields named in the transcript; these are genuine
local proof bodies, not wrapper surfaces.

Proof-doc status, 2026-05-17: the active compact blueprint and Wadj transcript
are the current control plane for Stage A, but the producer is not closed until
the proof-local ordinary and raw-adjacent fixed-test selections, endpoint
DCT/carrier-pairing cancellations, moving-test perturbations, and
overlap-centered branch seeds are assembled inside the direct
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` body.  The live gap is
the `hzero_plus`/`hzero_minus` branch/source side-height proof; if Lean exposes
a missing support fact, add only the narrow neutral support lemma matching this
transcript.  Do not add a public side-transfer, `AdjEdge = OrdEdge`, `Wadj`,
`Hdiff`, common-boundary, or final theorem-2 wrapper.

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
