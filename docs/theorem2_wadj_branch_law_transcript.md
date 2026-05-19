# Wadj Branch-Law Transcript for Stage A

Status: live proof transcript for the first Stage-A blocker in
`docs/theorem2_e_to_r_closure_blueprint.md`.

Target theorem:

```lean
BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45
```

This note expands only the proof-local construction of the adjacent
all-overlap seed `Wadj`.  It is not a new production carrier, not a theorem
wrapper, and not a standalone monodromy package.  The witnesses below should
live inside the direct proof unless a genuinely neutral SCV lemma is split out.

## Output Needed Inside the Hdiff Proof

For two selected local elements `A` and `B`, and a point
`z0 in A.N inter B.N`, the direct proof must construct:

```lean
have hord_seed :
    exists Word : Set (Fin n -> Fin (d + 1) -> Complex),
      IsOpen Word /\
      z0 in Word /\
      Word <= A.N inter B.N /\
      Set.EqOn A.Ord B.Ord Word := by
  -- ordinary-sector branch-seed proof below

have hadj_seed :
    exists Wadj : Set (Fin n -> Fin (d + 1) -> Complex),
      IsOpen Wadj /\
      z0 in Wadj /\
      Wadj <= A.N inter B.N /\
      Set.EqOn A.Adj B.Adj Wadj := by
  -- adjacent-sector branch-seed proof below
```

Then the already checked SCV helper gives the difference overlap:

```lean
have hDiff :
    Set.EqOn
      (fun z => A.Adj z - A.Ord z)
      (fun z => B.Adj z - B.Ord z)
      (A.N inter B.N) := by
  -- rewrite A.N and B.N by their metric-ball fields
  exact
    SCV.identity_theorem_product_inter_metric_ball_sub_of_two_eqOn_open
      hWadj_open hz0Wadj hWadj_sub
      hWord_open hz0Word hWord_sub
      A.Adj_holo A.Ord_holo B.Adj_holo B.Ord_holo
      hWadj_eq hWord_eq
```

The hard work is only the construction of `Word` and `Wadj`.  The final SCV
propagation is already checked in `OSReconstruction/SCV/OverlapIdentity.lean`.

## Proof-Local Branch Kinds

Use two branch kinds only:

```text
ordinary41
adjacent412
```

For `ordinary41`, the initial local domain and branch are:

```text
OmegaOrd0 := BHW.ExtendedTube d n inter H.OmegaJ
BOrd0 z   := BHW.extendF (bvt_F OS lgc n) z
```

The terminal ordinary branch is compared on the ordinary sheet:

```text
OrdSheet := BHW.ExtendedTube d n
OrdGlobal z := BHW.extendF (bvt_F OS lgc n) z
```

For `adjacent412`, the initial local domain and branch are the corrected OS-I
section 4.12 data, but in two layers.  The raw seed window is:

```text
OmegaSeed412 :=
  { z | BHW.permAct (d := d) P.τ z in BHW.ForwardTube d n } inter H.OmegaJ

BSeed412 z :=
  bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
```

This raw seed window is centered at the genuine adjacent seed point
`zadj = BHW.permAct P.τ zord`, not at the ordinary Wick point `zord`.
The usable initial data for the adjacent one-branch chain is the transported
OS-I `(4.12)` analytic element:

```lean
OmegaAdj0 : Set (Fin n -> Fin (d + 1) -> Complex)
BAdj0     : (Fin n -> Fin (d + 1) -> Complex) -> Complex

OmegaAdj0_open       : IsOpen OmegaAdj0
OmegaAdj0_connected  : IsConnected OmegaAdj0
OmegaAdj0_sub_hull   : OmegaAdj0 <= H.OmegaJ
zord_mem_OmegaAdj0   : zord in OmegaAdj0
BAdj0_holo           : DifferentiableOn Complex BAdj0 OmegaAdj0
BAdj0_wick_trace     :
  BAdj0 zord =
    bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k)))

seed412 :
  exists Wseed : Set (Fin n -> Fin (d + 1) -> Complex),
    IsOpen Wseed /\
    Wseed.Nonempty /\
    Wseed <= OmegaAdj0 inter OmegaSeed412 /\
    Set.EqOn BAdj0 BSeed412 Wseed
```

The terminal adjacent branch is compared on:

```text
AdjSheet := BHW.permutedExtendedTubeSector d n P.τ
```

There is no upstream global formula for the adjacent branch in this stage.
The later deterministic branch using `extendF` after the permutation action is
downstream-only for Stage A.

The flat bridge uses the checked flat common-chart domains:

```text
FlatPlus  := BHW.os45FlatCommonChartOmega d n 1
FlatMinus := BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)
FlatEdge  := BHW.os45FlatCommonChartEdgeSet d n P 1
FlatCone  := BHW.os45FlatCommonChartCone d n
```

and the checked ambient bridge:

```lean
BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
```

`BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_continuousBoundaryOn`
is also checked, but it is not the active Stage-A target unless the OS-I
`(4.14)` argument is strengthened all the way to a common continuous boundary
function.  The current strict target is the distributional
local zero-height pairings `hzero_plus` and `hzero_minus`, which feed the
checked local zero-height bridge directly.

## Adjacent 4.12 Seed-To-Wick Circuit

This is the first implementation block inside the direct `Hdiff` producer.  It
is proof-local, not a new wrapper theorem.

For the source point `x` attached to the selected path, set:

```lean
let gamma : unitInterval -> Fin n -> Fin (d + 1) -> Complex :=
  BHW.os45Figure24IdentityPath (d := d) (n := n) x

let zord : Fin n -> Fin (d + 1) -> Complex := gamma 0
let pord : Fin n -> Fin (d + 1) -> Complex := gamma 1
let zadj : Fin n -> Fin (d + 1) -> Complex :=
  BHW.permAct (d := d) P.τ zord
let padj : Fin n -> Fin (d + 1) -> Complex :=
  BHW.permAct (d := d) P.τ pord

let OmegaSeed412 : Set (Fin n -> Fin (d + 1) -> Complex) :=
  {z | BHW.permAct (d := d) P.τ z in BHW.ForwardTube d n} inter H.OmegaJ

let BSeed412 : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
```

Checked seed data already available:

```lean
have hseed_mem : zadj in OmegaSeed412 := by
  -- rewrite zord = fun k => wickRotatePoint (x k)
  -- rewrite zadj = fun k => wickRotatePoint (x (P.τ k))
  -- use H.adjacentWick_mem_OS412SeedWindow x hxP

have hseed_open : IsOpen OmegaSeed412 := by
  -- BHW.isOpen_permAct_preimage_forwardTube intersect H.OmegaJ_open

have hseed_holo :
    DifferentiableOn Complex BSeed412 OmegaSeed412 := by
  -- H.differentiableOn_OS412SeedBranch OS lgc

have hseed_value :
    BSeed412 zadj =
      bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  -- BHW.os45Figure24_OS412SeedBranch_adjacentWick_eq_ordinaryWick
```

Forbidden shortcut:

```lean
-- Do not try to prove:
--   zord in OmegaSeed412
-- The checked theorem
--   H.ordinaryWick_not_mem_OS412SeedWindow x hxP
-- rules this out.
```

The required output of the circuit is:

```lean
have hadj412 :
    exists (OmegaAdj0 : Set (Fin n -> Fin (d + 1) -> Complex))
      (BAdj0 : (Fin n -> Fin (d + 1) -> Complex) -> Complex),
      IsOpen OmegaAdj0 /\
      IsConnected OmegaAdj0 /\
      OmegaAdj0 <= H.OmegaJ /\
      zord in OmegaAdj0 /\
      DifferentiableOn Complex BAdj0 OmegaAdj0 /\
      BAdj0 zord =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) /\
      (exists Wseed : Set (Fin n -> Fin (d + 1) -> Complex),
        IsOpen Wseed /\
        Wseed.Nonempty /\
        Wseed <= OmegaAdj0 inter OmegaSeed412 /\
        Set.EqOn BAdj0 BSeed412 Wseed) /\
      (forall W : Set (Fin n -> Fin (d + 1) -> Complex),
        IsOpen W -> zord in W -> W <= H.OmegaJ ->
          exists (C0 : Set (Fin n -> Fin (d + 1) -> Complex))
            (C0branch : (Fin n -> Fin (d + 1) -> Complex) -> Complex)
            (r : Real),
            0 < r /\
            C0 = Metric.ball zord r /\
            zord in C0 /\
            C0 <= OmegaAdj0 inter W /\
            DifferentiableOn Complex C0branch C0 /\
            Set.EqOn C0branch BAdj0 C0) := by
  -- Four-piece OS-I circuit below.
```

The four pieces are:

1. **Seed chart at `zadj`.**  Use the checked
   `H.OS412SeedWindow_metricBallChartInWindow OS lgc hxP` to get a metric
   ball in `OmegaSeed412` around `zadj`, with branch `BSeed412`.
2. **Adjacent corridor from `zadj` to `padj`.**  Use the checked two-sheet
   geometry
   `BHW.os45Figure24_joined_adjacentWick_to_adjLift0_initialSectorOverlap`,
   `BHW.os45Figure24_joined_adjLift0_to_adjLift1_initialSectorOverlap`,
   `BHW.os45Figure24_joined_adjLift_to_permActIdentityPath_initialSectorOverlap`,
   and
   `BHW.os45Figure24_joined_permActOrdinaryWick_to_permActCommonEdge_initialSectorOverlap`.
   This supplies domains and metric-ball shrink points only.  Branch equality
   is still the retained `(4.12)` adjacent-sector transfer.
3. **Flat common-edge crossover from `padj` to `pord`.**  Prove the local
   zero-height pairings `hzero_plus` and `hzero_minus` for the current ordinary
   and transported adjacent analytic elements from the ordinary/raw-adjacent
   side-height branch/source transfers plus the checked common source limit,
   and call
   `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`.
   The returned ambient seed is then intersected with the current incoming and
   outgoing metric balls.
4. **Ordinary return from `pord` to `zord`.**  Use the checked ordinary
   Figure-2-4 corridor
   `BHW.os45Figure24_joined_ordinaryWick_to_commonEdge_initialSectorOverlap`
   in reverse, with ordinary-sector transfer against `BOrd0`.

After these four pieces, glue the proof-local finite family by
`SCV.glued_iUnion`, prove holomorphy by
`SCV.differentiableOn_glued_iUnion`, and use the endpoint-centered ordinary
Wick chart to prove `BAdj0_wick_trace`.  Only this `hadj412` output may serve
as the adjacent initial data for the later one-branch chain from `zord` to an
arbitrary terminal point `q`.

### Implementation Obligations Inside `hadj412`

The `hadj412` circuit must inline these internal subproofs in its proof body;
they are the local mathematical obligations that replace any public wrapper:

1. `adjacent_sector_seed_transport`: given two metric-ball charts inside the
   selected adjacent sheet, both carrying the retained continuation of
   `BSeed412`, produce a nonempty complex-open equality seed on their overlap.
   This is the local Hall-Wightman analytic-element uniqueness step.  It is
   not a topological connectedness argument and it is not the deterministic
   `extendF` after permutation.
2. proof-local flat zero-height pairing block: for a local flat edge window
   `E`, construct `Tlocal`, `hzero_plus`, and `hzero_minus` from
   the OS-I `(4.14)` side-height branch/source transfer for the ordinary
   `(4.1)` side and genuine adjacent `(4.12)` side.  The checked
   source-pairing equality
   `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick` is used
   later as a Wick-seed equality, not as a flat zero-height normalization.
   The output must match exactly the inputs of
   `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`.
3. `circuit_gallery_glue`: concatenate the seed chart, adjacent corridor
   charts, flat crossover chart, and ordinary return charts into one finite
   metric-ball gallery, prove all pairwise overlaps by
   `SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds`, then glue
   by `SCV.glued_iUnion`.

If any of these three subproofs is missing, do not start the public
`Hdiff` theorem.  The next implementation should target the first missing
subproof directly inside the local file, or split out a neutral SCV finite
gallery helper only if it is independent of OS/BHW/Figure-2-4 provenance.

### Lean-Ready Private Data Contract

The first Lean file for the direct producer may introduce private helper
records in the downstream companion file.  These are data-shape aids, not
mathematical wrappers: every field below is proved in the same file from the
checked geometry, OS-I boundary data, and SCV identity theorems.

Use the following local abbreviations throughout the proof:

```lean
abbrev Z := Fin n -> Fin (d + 1) -> Complex

let OrdGlobal : Z -> Complex :=
  BHW.extendF (bvt_F OS lgc n)

let Raw412 : Z -> Complex :=
  fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)

let AdjEndpoint : Z -> Complex :=
  fun z => BHW.extendF (bvt_F OS lgc n)
    (BHW.permAct (d := d) P.τ z)
```

The branch-kind tag is only a proof-local discriminator:

```lean
inductive BranchKind where
  | ordinary41
  | adjacent412

def kindSheet : BranchKind -> Set Z
  | .ordinary41 => BHW.ExtendedTube d n
  | .adjacent412 => BHW.permutedExtendedTubeSector d n P.τ

def initialCarrier : BranchKind -> Set Z
  | .ordinary41 => OmegaOrd0
  | .adjacent412 => OmegaAdj0

def initialBranch : (k : BranchKind) -> Z -> Complex
  | .ordinary41 => BOrd0
  | .adjacent412 => BAdj0
```

Every chart used by the finite galleries must now use the checked private Hdiff
format, not an older standalone chart record.  In Lean, write

```lean
abbrev Z := Fin n -> Fin (d + 1) -> Complex
abbrev Chart := PointedMetricBranchChart Z Complex
```

and use the checked private fields and lemmas:

```lean
(A : Chart)
A.center
A.radius
A.branch
A.holo
A.carrier
A.carrier_open
A.center_mem
A.restrict_center
```

Open overlap seeds are stored by the checked private type

```lean
PointedSeedEdge z0 A.carrier B.carrier A.branch B.branch
```

and are consumed only by the checked finite pointed-gallery helpers
`pointed_seed_gallery_endpoint_seed_chart`,
`pointed_metric_seed_of_restricted_gallery_pair`,
`PointedMetricBranchChart.eqOn_inter_of_seed`, and
`PointedMetricBranchChart.sub_eqOn_inter_of_two_seeds`.  Do not reintroduce a
separate public chart/germ wrapper for this purpose.

The one-branch witness in the proof should therefore be a local structure or
tuple named `Chain kind`, whose chart fields are exactly `Chart`.  Its terminal
fields are just notation for the last chart:

```lean
chainOrd.terminalChart : Chart
chainOrd.terminalCarrier := chainOrd.terminalChart.carrier
chainOrd.terminalBranch := chainOrd.terminalChart.branch
chainOrd.terminalCarrier_open := chainOrd.terminalChart.carrier_open
chainOrd.terminalBranch_holo := chainOrd.terminalChart.holo

chainAdj.terminalChart : Chart
chainAdj.terminalCarrier := chainAdj.terminalChart.carrier
chainAdj.terminalBranch := chainAdj.terminalChart.branch
chainAdj.terminalCarrier_open := chainAdj.terminalChart.carrier_open
chainAdj.terminalBranch_holo := chainAdj.terminalChart.holo
```

Any retained provenance field must either be an actual `PointedSeedEdge` at the
current observed point, or enough raw one-branch data to build one by
retargeting with `PointedMetricBranchChart.restrict_center`.  A field named
`pair_seed` is not an assumption to import from elsewhere; it is the in-body
result of the ordinary-sector, adjacent-sector, and flat-transfer case split
below.

The corrected adjacent circuit exports a concrete private packet:

```lean
structure Adj412CircuitOutput where
  OmegaAdj0 : Set Z
  BAdj0 : Z -> Complex
  OmegaAdj0_open : IsOpen OmegaAdj0
  OmegaAdj0_connected : IsConnected OmegaAdj0
  OmegaAdj0_sub_hull : OmegaAdj0 <= H.OmegaJ
  zord_mem : zord in OmegaAdj0
  BAdj0_holo : DifferentiableOn Complex BAdj0 OmegaAdj0
  seed_eq_raw412 :
    exists Wseed : Set Z,
      IsOpen Wseed /\
      Wseed.Nonempty /\
      Wseed <= OmegaAdj0 inter OmegaSeed412 /\
      Set.EqOn BAdj0 Raw412 Wseed
  wick_trace :
    BAdj0 zord =
      bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k)))
  pointedChartInWindow :
    forall W : Set Z, IsOpen W -> zord in W -> W <= H.OmegaJ ->
      exists C0 : Chart,
        C0.center = zord /\
        C0.carrier <= OmegaAdj0 inter W /\
        Set.EqOn C0.branch BAdj0 C0.carrier
```

When the proof later works over a source window `Ulocal`, endpoint-centered
trace fields are derived from this packet and retained in the corresponding
local adjacent chain tuple:

```lean
terminal_contains_adjacentWick :
  forall u, u in P.V ->
    (fun k => wickRotatePoint (u k)) in chainAdj.terminalCarrier

terminal_adjacentWick_trace :
  forall u, u in P.V ->
    chainAdj.terminalBranch (fun k => wickRotatePoint (u k)) =
      bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k)))

terminal_contains_adjacentCommonEdge :
  forall u, u in P.V ->
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u)) in chainAdj.terminalCarrier

terminal_eq_raw412_seed :
  Set.EqOn chainAdj.terminalBranch Raw412 chainAdj.terminalCarrier
```

The ordinary chain carries the analogous `terminal_contains_ordinaryWick`,
`terminal_contains_ordinaryCommonEdge`, and `terminal_eq_ordinary_global`
local facts.  Boundary-value selection is not a chain field: it is proved later
by the fixed-test finite induction from `ordinary41_fixed_test_boundaryValue_extendF`.

The neutral path support now available in the import closure is this checked
pure topology statement in `OSReconstruction/SCV/ConnectedNeighborhood.lean`:

```lean
theorem SCV.exists_open_connected_neighborhood_of_joinedIn_subset_open
    {E : Type*} [TopologicalSpace E] [LocallyCompactSpace E] [RegularSpace E]
    [LocallyConnectedSpace E]
    {Omega : Set E} {a b : E}
    (hOmega_open : IsOpen Omega)
    (hjoin : JoinedIn Omega a b) :
    exists U : Set E,
      IsOpen U /\ IsConnected U /\ a in U /\ b in U /\ U <= Omega
```

Its proof is compactness and connectedness of the `JoinedIn.somePath` image
followed by the checked compact-connected-open-neighborhood theorem.  Endpoint
and overlap balls are obtained later by combining this open carrier with
`SCV.exists_metric_ball_subset_inter_of_mem_open`.  When the branch itself must
be retargeted to such an endpoint-centered ball, use the checked neutral
restriction helper:

```lean
theorem SCV.exists_metric_ball_differentiableOn_subset_of_mem_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
    [NormedAddCommGroup F] [NormedSpace Complex F]
    {U : Set E} {z : E} {f : E -> F}
    (hU : IsOpen U) (hz : z in U) (hf : DifferentiableOn Complex f U) :
    exists r : Real, 0 < r /\ Metric.ball z r <= U /\
      DifferentiableOn Complex f (Metric.ball z r)
```

Both helpers have no OS/BHW content; they are the permitted neutral support
splits before the direct Hdiff body.

## Lean-Facing Transcript For The Three `hadj412` Subproofs

This section is the implementation transcript for the three proof-local
subproofs above.  The live Lean work is isolated in the adjacent
analytic-element uniqueness seed and in the OS-I `(4.14)` source
zero-representation block below.  The names below are local `have` blocks
inside the eventual proof of
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`; they are not public
theorem surfaces unless the proof genuinely needs a neutral support lemma with
the same mathematical content.

### `adjacent_sector_seed_transport`

The adjacent transport datum is now expressed entirely in the checked private
pointed-chart language.  A terminal adjacent chart is a `Chart`; its retained
raw provenance is not a new public record but the proof-local data needed to
produce pointed edges out of the three allowed sources:

The local binder name in the transcript is `Adj412RawProvenance A`.  It is not
implemented as an exported definition unless Lean needs a local structure for
bookkeeping.  Its fields, if materialized, are exactly the retained raw
`(4.12)` one-branch gallery from `OmegaAdj0/BAdj0` to `A`, the endpoint
retargeting data consumed by `pointed_seed_edge_retarget_both`, and the proof
that `A.branch` is the transported raw analytic element rather than a premature
definition by `extendF o permAct`.

The local adjacent seed between two retained charts is no longer stated as an
extra theorem.  It is the immediate consumer call below, with the finite OS45
work isolated in the `hgrid` argument required by the checked private helper:

```lean
have adjacent_sector_seed_transport
    (A B : Chart) {z0 : Z}
    (hzA : z0 in A.carrier) (hzB : z0 in B.carrier)
    (hAraw : Adj412RawProvenance A)
    (hBraw : Adj412RawProvenance B) :
    exists W, IsOpen W /\ z0 in W /\
      W <= A.carrier inter B.carrier /\
      Set.EqOn A.branch B.branch W := by
  refine pointed_metric_seed_of_restricted_gallery_pair A B hzA hzB ?hgrid
  intro A0 B0 hA0_center hA0_sub hB0_center hB0_sub
  -- Expand the `hgrid` field block below here.  It constructs a
  -- `PointedCommonCenterGalleryPair Z Complex z0` from the retained raw
  -- provenance of `A` and `B` plus the four restriction facts above.
```

The local `hgrid` goal is expanded in the same proof block as a construction of

```lean
exists G : PointedCommonCenterGalleryPair Z Complex z0,
  G.left 0 = A0 /\ G.right 0 = B0
```

for arbitrary endpoint-centered restrictions `A0` and `B0`.  Every edge in the
two finite pointed galleries stored by `G` is a checked `PointedSeedEdge`; the
edge is produced by exactly one of these sources:

```text
retained raw (4.12) provenance:
  pointed_seed_edge_retarget_both

ordinary/common-model overlap:
  pointed_seed_edge_of_common_model

flat real-Jost EOW crossing:
  flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM
```

The flat crossing may be used only after the proof-local local zero-height
pairings `hzero_plus` and `hzero_minus` have been proved for the current flat
edge window.  The raw case may use only retained `OmegaSeed412/BSeed412`
provenance and endpoint retargeting.  No edge may assume `Wadj`, `Hdiff`, a
common-boundary CLM, a full source-window representation wrapper, or the
deterministic downstream adjacent branch.

Implementation note, corrected by the 2026-05-17
`deep-research-max-preview-04-2026` audit
`v1_ChZEZ1FKYW9pWEFjYTV4TjhQd2QtWU9BEhZEZ1FKYW9pWEFjYTV4TjhQd2QtWU9B`:
the formerly named adjacent uniqueness block is an in-body proof block, not an
input to assume.  The audit confirms the overlap-centered route is
mathematically viable, but only after the proof supplies explicit
path-independence data.  It is not enough to say that two terminal charts share
the raw `(4.12)` seed and meet at `z0`.

The Lean transcript therefore uses a single proof-local `hgrid` contract:
given arbitrary endpoint-centered restrictions of the two terminal charts,
construct a `PointedCommonCenterGalleryPair Z Complex z0`.  The already checked
private consumer `pointed_metric_seed_of_restricted_gallery_pair` performs the
endpoint retargeting, finite pointed-chain propagation, and final open seed
extraction.  The OS45 work that remains is exactly the construction of the
finite pair `G` from retained raw provenance, ordinary/common-model overlap,
and the flat real-Jost EOW seed.

Hard-gap correction, 2026-05-17: every comparison gallery is pointed at the
observed overlap point `z0`.  The checked consumer already proves the finite
pointed induction and shrinks all neighborhoods at the end.  The direct proof
must only provide the `PointedCommonCenterGalleryPair` requested by `hgrid`,
with all edge seeds open and containing the same `z0`.  No all-pair seed,
monodromy theorem, pre-built `Wadj`, or pre-built `Hdiff` enters this consumer.

The finite `G` construction is the strict local replacement for a monodromy
wrapper.  It is proved inside
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` from the retained
raw one-branch galleries, endpoint retargeting balls, ordinary common-model
overlaps, and the flat real-Jost EOW transfer.  If Lean wants names for the
edge cases, they are local `have` blocks only; their conclusions must be
checked `PointedSeedEdge` values that feed `G.left_step` or `G.right_step`.

Lean status, 2026-05-17: the neutral private helpers
`pointed_seed_gallery_endpoint_seed`,
`PointedCommonCenterGalleryPair.endpoint_seed`,
`pointed_retargeted_gallery_pair_seed`, and
`pointed_metric_seed_of_restricted_gallery_pair` are now checked in
`OSToWightmanLocalityOS45Figure24Hdiff.lean`, together with the Nat/Fin
finite-chain propagation lemmas they use.  The endpoint retargeting edge
`A -> A0` / `B -> B0` is checked privately there as
`PointedMetricBranchChart.restrict_center`: it shrinks any metric-ball chart
around an observed `z0` and returns the pointed restriction seed without adding
any OS/BHW conclusion.  The checked consumer now takes the exact local contract
needed by `hgrid`: after retargeting both terminal charts to `z0`, a finite
pointed common-center gallery pair yields the open overlap seed between the
original terminal branches.

The downstream identity-theorem consumers are also checked privately:
`PointedMetricBranchChart.eqOn_inter_of_seed` propagates one pointed seed to the
full overlap of two product metric-ball charts, and
`PointedMetricBranchChart.sub_eqOn_inter_of_two_seeds` propagates the two seeds
needed for the difference branch.  These helpers keep the all-overlap SCV
identity theorem downstream of the adjacent seed construction.  The remaining
Lean work in this block is to feed the consumer the actual OS45 pointed edge
seeds from `hgrid`: retained raw `(4.12)` provenance, ordinary/common-model
overlap, and the upstream flat real-Jost EOW seed.

The initial chart inputs are also now Lean-backed in the private chart format:
`OS45BHWJostHullData.ordinaryWick_pointedChartInWindow` packages the ordinary
`(4.1)` metric-ball chart, and
`OS45BHWJostHullData.OS412SeedWindow_pointedChart` packages the corrected raw
adjacent `(4.12)` seed chart inside the two-sheet initial overlap.  These are
adapters from checked OS-I chart constructors to the proof-local
`PointedMetricBranchChart` type, not replacements for the raw adjacent
continuation or deterministic endpoint branch.

Lean status, 2026-05-17 flat/common/raw edge producers: the three local edge
sources needed by the grid now have checked private consumers in the Hdiff
companion.  `pointed_seed_edge_of_common_model` is the ordinary/common-model
case; `pointed_seed_edge_retarget_both` transports a retained raw provenance
edge through the endpoint-centered restrictions used by the pointed grid; and
`flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM` consumes the
checked local zero-height EOW reducer together with the two chart-to-model
equalities to produce the actual `PointedSeedEdge` for a flat real-Jost crossing.
The flat helper uses only `hzero_plus`/`hzero_minus` against the local CLM
`Tlocal`; it does not assume `Wadj`, `Hdiff`, or a common-boundary CLM.

Wrapper-removal update, 2026-05-17: the private
`flat_realJost_EOW_pointed_seed_of_sourceRepresentsOn` and
`sourceRepresentsOn_of_flat_commonBoundary_zero` detours have been removed from
the Hdiff companion.  They were not needed for the upstream flat crossing and
would encourage re-packaging the real blocker as a source-representation
wrapper.  The Lean-facing flat edge now takes the direct local zero-height
pairing data `E`, `Tlocal`, `hzero_plus`, and `hzero_minus`.

The local construction before this consumer is field-by-field and stays inside
the same proof.  The `have` below is the exact Lean shape to enter:

```lean
have hgrid
    (A B : Chart) {z0 : Z}
    (hAraw : Adj412RawProvenance A)
    (hBraw : Adj412RawProvenance B) :
    forall (A0 B0 : Chart),
      A0.center = z0 ->
      A0.carrier <= A.carrier ->
      B0.center = z0 ->
      B0.carrier <= B.carrier ->
        exists G : PointedCommonCenterGalleryPair Z Complex z0,
          G.left 0 = A0 /\ G.right 0 = B0 := by
  intro A0 B0 hA0_center hA0_sub hB0_center hB0_sub

  -- The local case split below constructs the `PointedCommonCenterGalleryPair`
  -- structure literal directly.  There is no public gallery theorem and no
  -- abstract chain packet in scope.
```

When Lean expands the finite-gallery field block, every edge must be one of:

* a retained raw `(4.12)` edge transported through
  `pointed_seed_edge_retarget_both`;
* an ordinary/common-model overlap edge from `pointed_seed_edge_of_common_model`;
* a flat real-Jost crossing edge from
  `flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM`, after the
  local zero-height plus/minus pairings have been proved.

The field block itself should be copied into Lean in this order.

```lean
-- Local edge constructors, all inside the `hgrid` body.
have edge_raw
    {A1 A2 A1' A2' : Chart}
    (hA1' :
      PointedSeedEdge z0 A1.carrier A1'.carrier A1.branch A1'.branch)
    (hraw :
      PointedSeedEdge z0 A1.carrier A2.carrier A1.branch A2.branch)
    (hA2' :
      PointedSeedEdge z0 A2.carrier A2'.carrier A2.branch A2'.branch) :
    PointedSeedEdge z0 A1'.carrier A2'.carrier A1'.branch A2'.branch := by
  exact pointed_seed_edge_retarget_both hA1' hraw hA2'

have edge_common
    {A1 A2 : Chart} (hz1 : z0 in A1.carrier) (hz2 : z0 in A2.carrier)
    (hA1_model : Set.EqOn A1.branch OrdGlobal A1.carrier)
    (hA2_model : Set.EqOn A2.branch OrdGlobal A2.carrier) :
    PointedSeedEdge z0 A1.carrier A2.carrier A1.branch A2.branch := by
  exact pointed_seed_edge_of_common_model
    A1.carrier_open A2.carrier_open hz1 hz2
    hA1_model hA2_model

have edge_flat
    {A1 A2 : Chart}
    (E : Set (BHW.OS45FlatCommonChartReal d n))
    (hE_open : IsOpen E)
    (hE_sub :
      E <= BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
    (ys : Fin (BHW.os45FlatCommonChartDim d n) ->
      Fin (BHW.os45FlatCommonChartDim d n) -> Real)
    (hys_mem : forall j, ys j in BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent Real ys)
    (x0 : BHW.OS45FlatCommonChartReal d n) (hx0 : x0 in E)
    (Tlocal : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
        ->L[Complex] Complex)
    (hzero_plus : forall phi, HasCompactSupport (phi : _ -> Complex) ->
      tsupport (phi : _ -> Complex) <= E ->
      integral (fun x => BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex)) * phi x)
        = Tlocal phi)
    (hzero_minus : forall phi, HasCompactSupport (phi : _ -> Complex) ->
      tsupport (phi : _ -> Complex) <= E ->
      integral (fun x => BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (fun a => (x a : Complex)) * phi x) = Tlocal phi)
    (hz0_flat :
      z0 =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed x0)))
    (hzA :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) in A1.carrier)
    (hzB :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) in A2.carrier)
    (hA1_model :
      Set.EqOn A1.branch (BHW.extendF (bvt_F OS lgc n)) A1.carrier)
    (hA2_model :
      Set.EqOn A2.branch
        (fun z => BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z)) A2.carrier) :
    PointedSeedEdge z0 A1.carrier A2.carrier A1.branch A2.branch := by
  simpa [hz0_flat] using
    flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM
      (d := d) hd OS lgc (P := P)
      (E := E) hE_open hE_sub ys hys_mem hys_li x0 hx0
      Tlocal hzero_plus hzero_minus A1 A2 hzA hzB hA1_model hA2_model
```

The pointed gallery is local at the actual overlap point `z0`.  Do not replay
a previously chosen global path unless every carrier in that replay has first
been retargeted to contain `z0`; that retargeting is exactly what the checked
consumer is asking for.  The implementation therefore performs a local
OS-I/Figure-2-4 case split at `z0`, chooses one canonical chart `Ccommon` in
the selected local window, and builds two short galleries from `A0` and `B0`
to that same `Ccommon`.

The local case split is proof-local.  In Lean it can be written either as a
small local inductive in a `where` block or as nested `rcases`; it must not be
exported.  Its branches contain exactly the data already produced by
`local_transfer_step` at `z0`:

```lean
-- Proof-local only; not a theorem surface.
structure OrdModelAtZ0 (A : Chart) where
  z0_mem : z0 in A.carrier
  eq_ord :
    Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier

structure RawRetargetAtZ0 (A rawLocal : Chart) where
  z0_mem : z0 in A.carrier
  edge_to_raw :
    PointedSeedEdge z0 A.carrier rawLocal.carrier
      A.branch rawLocal.branch

structure FlatMinusAtZ0 (A Cminus : Chart) where
  z0_mem : z0 in A.carrier
  to_Cminus_edge :
    PointedSeedEdge z0 A.carrier Cminus.carrier A.branch Cminus.branch

structure FlatCrossingAtZ0 (z0 : Z) (Cplus Cminus : Chart) where
  E : Set (BHW.OS45FlatCommonChartReal d n)
  hE_open : IsOpen E
  hE_sub :
    E <= BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n))
  ys : Fin (BHW.os45FlatCommonChartDim d n) ->
    Fin (BHW.os45FlatCommonChartDim d n) -> Real
  hys_mem : forall j, ys j in BHW.os45FlatCommonChartCone d n
  hys_li : LinearIndependent Real ys
  x0 : BHW.OS45FlatCommonChartReal d n
  hx0 : x0 in E
  Tlocal : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
      ->L[Complex] Complex
  hzero_plus : forall phi, HasCompactSupport (phi : _ -> Complex) ->
    tsupport (phi : _ -> Complex) <= E -> OrdEdge phi = Tlocal phi
  hzero_minus : forall phi, HasCompactSupport (phi : _ -> Complex) ->
    tsupport (phi : _ -> Complex) <= E -> AdjEdge phi = Tlocal phi
  hz0_flat :
    z0 =
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0))
  hzCplus : z0 in Cplus.carrier
  hzCminus : z0 in Cminus.carrier
  hCplus_model :
    Set.EqOn Cplus.branch (BHW.extendF (bvt_F OS lgc n)) Cplus.carrier
  hCminus_model :
    Set.EqOn Cminus.branch
      (fun z => BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.τ z)) Cminus.carrier

inductive LocalOverlapAtZ0 where
| ordinary
    (hA_ord : OrdModelAtZ0 A0)
    (hB_ord : OrdModelAtZ0 B0)
    (Ccommon : Chart)
    (hCcommon_ord : OrdModelAtZ0 Ccommon)
    (hzCcommon : z0 in Ccommon.carrier)
| adjacent
    (rawLocal : Chart)
    (hA_adj : RawRetargetAtZ0 A0 rawLocal)
    (hB_adj : RawRetargetAtZ0 B0 rawLocal)
    (hzRawLocal : z0 in rawLocal.carrier)
| flat_plus_minus
    (Cplus Cminus : Chart)
    (hflat : FlatCrossingAtZ0 z0 Cplus Cminus)
    (hA_plus : OrdModelAtZ0 A0)
    (hB_minus : FlatMinusAtZ0 B0 Cminus)
| flat_minus_plus
    (Cplus Cminus : Chart)
    (hflat : FlatCrossingAtZ0 z0 Cplus Cminus)
    (hA_minus : FlatMinusAtZ0 A0 Cminus)
    (hB_plus : OrdModelAtZ0 B0)
```

The adjacent branch uses the local raw chart `rawLocal` supplied by retained
`Adj412RawProvenance` after retargeting to `z0`; it is not the downstream
deterministic `extendF o permAct` endpoint chart.  The flat branch obtains
`hzero_plus` and `hzero_minus` from the side-height proof body in this same
`hadj412` construction before it calls the checked flat pointed edge.

With those local fields expanded, the actual `hgrid` body has this shape:

```lean
have edge_symm
    {A1 A2 : Chart}
    (h : PointedSeedEdge z0 A1.carrier A2.carrier A1.branch A2.branch) :
    PointedSeedEdge z0 A2.carrier A1.carrier A2.branch A1.branch := by
  exact
    { W := h.W
      W_open := h.W_open
      z0_mem := h.z0_mem
      W_sub := by
        intro z hz
        exact ⟨(h.W_sub hz).2, (h.W_sub hz).1⟩
      eqOn := by
        intro z hz
        exact (h.eqOn hz).symm }

obtain hcase :=
  local_overlap_case_at_z0 hAraw hBraw hA0_center hA0_sub
    hB0_center hB0_sub
cases hcase with
| ordinary hA_ord hB_ord Ccommon hCcommon_ord hzCcommon =>
    -- All three charts contain z0 and are restrictions inside
    -- `BHW.ExtendedTube d n ∩ H.ΩJ`.
    let leftLen : Nat := 1
    let rightLen : Nat := 1
    let left : Fin (leftLen + 1) -> Chart :=
      fun j => if (j : Nat) = 0 then A0 else Ccommon
    let right : Fin (rightLen + 1) -> Chart :=
      fun j => if (j : Nat) = 0 then B0 else Ccommon
    have hleft_step :
        forall j : Fin leftLen,
          PointedSeedEdge z0
            ((left (Fin.castSucc j)).carrier)
            ((left (Fin.succ j)).carrier)
            ((left (Fin.castSucc j)).branch)
            ((left (Fin.succ j)).branch) := by
      intro j
      fin_cases j
      exact edge_common hA_ord.z0_mem hzCcommon
        hA_ord.eq_ord hCcommon_ord.eq_ord
    have hright_step :
        forall j : Fin rightLen,
          PointedSeedEdge z0
            ((right (Fin.castSucc j)).carrier)
            ((right (Fin.succ j)).carrier)
            ((right (Fin.castSucc j)).branch)
            ((right (Fin.succ j)).branch) := by
      intro j
      fin_cases j
      exact edge_common hB_ord.z0_mem hzCcommon
        hB_ord.eq_ord hCcommon_ord.eq_ord
    have hleft_mem : forall j, z0 in (left j).carrier := by
      intro j
      fin_cases j
      · exact hA_ord.z0_mem
      · exact hzCcommon
    have hright_mem : forall j, z0 in (right j).carrier := by
      intro j
      fin_cases j
      · exact hB_ord.z0_mem
      · exact hzCcommon
    refine ⟨
      { leftLen := leftLen
        rightLen := rightLen
        center := Ccommon
        left := left
        right := right
        left_last_eq_center := by simp [left, leftLen]
        right_last_eq_center := by simp [right, rightLen]
        left_mem := hleft_mem
        right_mem := hright_mem
        left_step := hleft_step
        right_step := hright_step },
      by simp [left, leftLen],
      by simp [right, rightLen]⟩
| adjacent Ccommon hA_adj hB_adj hzCcommon =>
    -- All charts are local restrictions of the same transported raw `(4.12)`
    -- analytic element.  The edge is the retained raw provenance, retargeted
    -- through the endpoint-centered restrictions `A0` and `B0`.
    let leftLen : Nat := 1
    let rightLen : Nat := 1
    let left : Fin (leftLen + 1) -> Chart :=
      fun j => if (j : Nat) = 0 then A0 else Ccommon
    let right : Fin (rightLen + 1) -> Chart :=
      fun j => if (j : Nat) = 0 then B0 else Ccommon
    have hleft_step :
        forall j : Fin leftLen,
          PointedSeedEdge z0
            ((left (Fin.castSucc j)).carrier)
            ((left (Fin.succ j)).carrier)
            ((left (Fin.castSucc j)).branch)
            ((left (Fin.succ j)).branch) := by
      intro j
      fin_cases j
      exact hA_adj.edge_to_raw
    have hright_step :
        forall j : Fin rightLen,
          PointedSeedEdge z0
            ((right (Fin.castSucc j)).carrier)
            ((right (Fin.succ j)).carrier)
            ((right (Fin.castSucc j)).branch)
            ((right (Fin.succ j)).branch) := by
      intro j
      fin_cases j
      exact hB_adj.edge_to_raw
    have hleft_mem : forall j, z0 in (left j).carrier := by
      intro j
      fin_cases j
      · exact hA_adj.z0_mem
      · exact hzCcommon
    have hright_mem : forall j, z0 in (right j).carrier := by
      intro j
      fin_cases j
      · exact hB_adj.z0_mem
      · exact hzCcommon
    refine ⟨
      { leftLen := leftLen
        rightLen := rightLen
        center := Ccommon
        left := left
        right := right
        left_last_eq_center := by simp [left, leftLen]
        right_last_eq_center := by simp [right, rightLen]
        left_mem := hleft_mem
        right_mem := hright_mem
        left_step := hleft_step
        right_step := hright_step },
      by simp [left, leftLen],
      by simp [right, rightLen]⟩
| flat_plus_minus Cplus Cminus hflat hA_plus hB_minus =>
    -- The common chart is the plus/ordinary flat endpoint chart.  The left
    -- gallery compares A0 to Cplus by the ordinary model.  The right gallery
    -- compares B0 to Cminus by the adjacent model and then crosses from
    -- Cminus to Cplus by the upstream flat EOW seed.
    let Ccommon := Cplus
    let leftLen : Nat := 1
    let rightLen : Nat := 2
    let left : Fin (leftLen + 1) -> Chart :=
      fun j => if (j : Nat) = 0 then A0 else Cplus
    let right : Fin (rightLen + 1) -> Chart :=
      fun j =>
        if (j : Nat) = 0 then B0
        else if (j : Nat) = 1 then Cminus
        else Cplus
    have hflat_edge :
        PointedSeedEdge z0 Cplus.carrier Cminus.carrier
          Cplus.branch Cminus.branch :=
      edge_flat hflat.E hflat.hE_open hflat.hE_sub
        hflat.ys hflat.hys_mem hflat.hys_li hflat.x0 hflat.hx0
        hflat.Tlocal hflat.hzero_plus hflat.hzero_minus
        hflat.hz0_flat hflat.hzCplus hflat.hzCminus
        hflat.hCplus_model hflat.hCminus_model
    have hleft_step :
        forall j : Fin leftLen,
          PointedSeedEdge z0
            ((left (Fin.castSucc j)).carrier)
            ((left (Fin.succ j)).carrier)
            ((left (Fin.castSucc j)).branch)
            ((left (Fin.succ j)).branch) := by
      intro j
      fin_cases j
      exact edge_common hA_plus.z0_mem hflat.hzCplus
        hA_plus.eq_ord hflat.hCplus_model
    have hright_step :
        forall j : Fin rightLen,
          PointedSeedEdge z0
            ((right (Fin.castSucc j)).carrier)
            ((right (Fin.succ j)).carrier)
            ((right (Fin.castSucc j)).branch)
            ((right (Fin.succ j)).branch) := by
      intro j
      fin_cases j
      · exact hB_minus.to_Cminus_edge
      · exact edge_symm hflat_edge
    have hleft_mem : forall j, z0 in (left j).carrier := by
      intro j
      fin_cases j
      · exact hA_plus.z0_mem
      · exact hflat.hzCplus
    have hright_mem : forall j, z0 in (right j).carrier := by
      intro j
      fin_cases j
      · exact hB_minus.z0_mem
      · exact hflat.hzCminus
      · exact hflat.hzCplus
    refine ⟨
      { leftLen := leftLen
        rightLen := rightLen
        center := Ccommon
        left := left
        right := right
        left_last_eq_center := by simp [left, leftLen, Ccommon]
        right_last_eq_center := by simp [right, rightLen, Ccommon]
        left_mem := hleft_mem
        right_mem := hright_mem
        left_step := hleft_step
        right_step := hright_step },
      by simp [left, leftLen],
      by simp [right, rightLen]⟩
| flat_minus_plus Cplus Cminus hflat hA_minus hB_plus =>
    -- Same as the previous case with A/B interchanged.
    let Ccommon := Cplus
    let leftLen : Nat := 2
    let rightLen : Nat := 1
    let left : Fin (leftLen + 1) -> Chart :=
      fun j =>
        if (j : Nat) = 0 then A0
        else if (j : Nat) = 1 then Cminus
        else Cplus
    let right : Fin (rightLen + 1) -> Chart :=
      fun j => if (j : Nat) = 0 then B0 else Cplus
    have hflat_edge :
        PointedSeedEdge z0 Cplus.carrier Cminus.carrier
          Cplus.branch Cminus.branch :=
      edge_flat hflat.E hflat.hE_open hflat.hE_sub
        hflat.ys hflat.hys_mem hflat.hys_li hflat.x0 hflat.hx0
        hflat.Tlocal hflat.hzero_plus hflat.hzero_minus
        hflat.hz0_flat hflat.hzCplus hflat.hzCminus
        hflat.hCplus_model hflat.hCminus_model
    have hleft_step :
        forall j : Fin leftLen,
          PointedSeedEdge z0
            ((left (Fin.castSucc j)).carrier)
            ((left (Fin.succ j)).carrier)
            ((left (Fin.castSucc j)).branch)
            ((left (Fin.succ j)).branch) := by
      intro j
      fin_cases j
      · exact hA_minus.to_Cminus_edge
      · exact edge_symm hflat_edge
    have hright_step :
        forall j : Fin rightLen,
          PointedSeedEdge z0
            ((right (Fin.castSucc j)).carrier)
            ((right (Fin.succ j)).carrier)
            ((right (Fin.castSucc j)).branch)
            ((right (Fin.succ j)).branch) := by
      intro j
      fin_cases j
      exact edge_common hB_plus.z0_mem hflat.hzCplus
        hB_plus.eq_ord hflat.hCplus_model
    have hleft_mem : forall j, z0 in (left j).carrier := by
      intro j
      fin_cases j
      · exact hA_minus.z0_mem
      · exact hflat.hzCminus
      · exact hflat.hzCplus
    have hright_mem : forall j, z0 in (right j).carrier := by
      intro j
      fin_cases j
      · exact hB_plus.z0_mem
      · exact hflat.hzCplus
    refine ⟨
      { leftLen := leftLen
        rightLen := rightLen
        center := Ccommon
        left := left
        right := right
        left_last_eq_center := by simp [left, leftLen, Ccommon]
        right_last_eq_center := by simp [right, rightLen, Ccommon]
        left_mem := hleft_mem
        right_mem := hright_mem
        left_step := hleft_step
        right_step := hright_step },
      by simp [left, leftLen],
      by simp [right, rightLen]⟩
```

The names `local_overlap_case_at_z0`, `hA_ord`, `hA_adj`, `hflat`, and so on
are proof-local records produced by the three local transfer cases; they may
not assume the desired adjacent seed, `Wadj`, `Hdiff`, `chainOrd`, `chainAdj`,
or a deterministic adjacent endpoint branch.

This is the complete proof-doc contract for the adjacent uniqueness block.  The
checked private consumer supplies all finite pointed-chain induction.  The
implementation obligation here is exactly the OS45 construction of
`local_overlap_case_at_z0` from the ordinary-sector, adjacent-sector, or flat
real-Jost local transfer at the observed overlap point.

#### Adjacent seed shrink before the gallery

The raw `(4.12)` seed chart from
`H.OS412SeedWindow_metricBallChartInWindow OS lgc hxP` has carrier contained in

```lean
{z | BHW.permAct (d := d) P.τ z in BHW.ForwardTube d n} inter H.OmegaJ.
```

That raw window is the correct OS-I initial germ, but it is not by itself the
two-sheet overlap carrier needed for the Figure-2-4 gallery.  The shrink is now
checked as
`BHW.OS45BHWJostHullData.OS412SeedWindow_initialSectorOverlap_metricBallChart`:
it combines the raw `(4.12)` metric-ball chart with the checked point
membership

```lean
H.OS412Seed_mem_initialSectorOverlap x hxP :
  BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) in
    BHW.ExtendedTube d n inter BHW.permutedExtendedTubeSector d n P.τ
```

and the openness of both sheets.  The resulting first gallery carrier is:

```lean
let zseed := BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))
obtain <Cseed, Bseed, rseed, hrseed, hCseed_ball, hzseed_Cseed,
    hCseed_open, hCseed_pre, hCseed_raw_sub, hBseed_holo,
    hBseed_eq, hBseed_trace> :=
  H.OS412SeedWindow_initialSectorOverlap_metricBallChart OS lgc hxP
```

Only `Cseed/Bseed`, not the unshrunk raw seed window, enters the adjacent
one-branch gallery.  Its fields are then:

```lean
have hCseed_sub :
    Cseed <=
      ({z | BHW.permAct (d := d) P.τ z in BHW.ForwardTube d n} inter
        H.OmegaJ) inter
      (BHW.ExtendedTube d n inter
        BHW.permutedExtendedTubeSector d n P.τ) := by
  exact hCseed_raw_sub

have hCseed_twoSheet :
    Cseed <= BHW.ExtendedTube d n inter
      BHW.permutedExtendedTubeSector d n P.τ := by
  intro z hz
  exact (hCseed_raw_sub hz).2

have hBseed_holo : DifferentiableOn Complex Bseed Cseed := by
  exact hBseed_holo

have hBseed_trace :
    Bseed zseed = bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  exact hBseed_trace
```

This shrink is mathematical work, not a wrapper: it fixes the exact incoming
sheet domain for the genuine adjacent `(4.12)` chain.  It also explains why
the active route must not use the later deterministic adjacent branch as an
upstream seed.

### Proof-Local Flat Zero-Height Pairing Block

There are two flat EOW seeds in Stage A, and they must not be collapsed.

* **Upstream flat seed, inside `hadj412`.**  This crosses from the transported
  genuine adjacent `(4.12)` element at the horizontal adjacent side to the
  ordinary common-edge side.  Its input is the OS-I `(4.14)` compact-test
  boundary calculation below.  It produces the endpoint trace field
  `hadj412_common_trace`.
* **Downstream flat seed, after `h45_source_eqOn`.**  Once `Badj412` has both
  Wick and common-edge traces, `BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3`
  gives the local source common-edge equality `h45_source_eqOn`.  Only then may
  the proof call the checked consumer
  `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn`.

Using the downstream `sourceCommonEdge_eqOn` consumer inside the upstream
`hadj412` crossing would be circular: it requires the very common-edge equality
that `hadj412` is being built to make provable.  Conversely, the upstream
`(4.14)` compact-test calculation should not be repackaged as a public theorem
that assumes `h45_source_eqOn`, `Wadj`, or `Hdiff`.

For a flat crossing choose the source window first, then define the flat edge
as its image.  The local EOW bridge consumes tests supported in that image.

```lean
have hflat_zero_height_pairings :
    forall {Ulocal : Set (NPointDomain d n)}
      (hUlocal_open : IsOpen Ulocal)
      (hUlocal_sub : Ulocal <= P.V)
      (u0 : NPointDomain d n) (hu0 : u0 in Ulocal),
    let E : Set (BHW.OS45FlatCommonChartReal d n) :=
      BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) '' Ulocal
    IsOpen E /\
    E <= BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n)) /\
    exists Tlocal :
      SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex ->L[Complex] Complex,
      (forall phi,
        HasCompactSupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : Complex)) * phi x) =
          Tlocal phi) /\
      (forall phi,
        HasCompactSupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : Complex)) * phi x) =
          Tlocal phi) := by
  intro Ulocal hUlocal_open hUlocal_sub u0 hu0
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E := e '' Ulocal
  have hE_open : IsOpen E := by
    simpa [E, e] using e.toHomeomorph.isOpenMap Ulocal hUlocal_open
  have hE_sub :
      E <= BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x <u, hu, rfl>
    exact (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
      (1 : Equiv.Perm (Fin n)) u).mpr (hUlocal_sub hu)

  let Tlocal :=
    BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P

  let Fplus0 : BHW.OS45FlatCommonChartReal d n -> Complex := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex))

  let Fminus0 : BHW.OS45FlatCommonChartReal d n -> Complex := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      (fun a => (x a : Complex))
  -- `Fminus0` is the endpoint expression for the transported genuine
  -- adjacent `(4.12)` element.  It may be used here only after the chain
  -- provenance has proved equality with the branch transported from the raw
  -- `(4.12)` seed; it is not upstream initial data.

  have hFplus0_cont : ContinuousOn Fplus0 E := by
    -- differentiability of the ordinary flat branch plus
    -- `E <= os45FlatCommonChartOmega d n 1` on the real edge.

  have hFminus0_cont : ContinuousOn Fminus0 E := by
    -- differentiability of the selected adjacent flat branch plus
    -- `E <= os45FlatCommonChartOmega d n (P.τ.symm * 1)` on the real edge.

  have h414_pairings_to_Tlocal :
      (forall phi, HasCompactSupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : Complex)) * phi x) =
          Tlocal phi) /\
      (forall phi, HasCompactSupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : Complex)) * phi x) =
          Tlocal phi) := by
    -- For each compact flat test, prove the ordinary plus-side and raw
    -- adjacent minus-side branch/source asymptotic transfers, combine each
    -- with the checked source-side common limit, and apply
    -- `zeroHeight_pairings_eq_common_of_sideLimits`.

  have hzero_plus :
      forall phi, HasCompactSupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : Complex)) * phi x) =
          Tlocal phi := by
    intro phi hphi_compact hphiE
    exact h414_pairings_to_Tlocal.1 phi hphi_compact hphiE

  have h414_integrals :
      forall phi, HasCompactSupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : Complex)) * phi x) =
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : Complex)) * phi x) := by
    intro phi hphi_compact hphiE
    -- This is the flat `(4.14)` output of the proof-local OS-I side-height
    -- transfer, not a finite-side-height Schwinger identity and not a
    -- Wick/source normalization.
    exact (h414_pairings_to_Tlocal.2 phi hphi_compact hphiE).trans
      (h414_pairings_to_Tlocal.1 phi hphi_compact hphiE).symm

  have hzero_minus :
      forall phi, HasCompactSupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : Complex)) * phi x) =
          Tlocal phi := by
    intro phi hphi_compact hphiE
    exact h414_pairings_to_Tlocal.2 phi hphi_compact hphiE

  exact <hE_open, hE_sub, Tlocal, hzero_plus, hzero_minus>
```

The flat block has no public theorem shell left.  The proof-local
transition is the common-boundary calculation expanded next:

```text
proof-local flat transition:
  ∫ Fminus0 x * phi x = ∫ Fplus0 x * phi x
  for every compactly supported flat test with support in the current edge
  image E = os45CommonEdgeFlatCLE d n 1 '' Ulocal.

checked inputs used around the proof:
  edge-window and CLE support lemmas,
  the checked ordinary-edge representation,
  BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM,
  and endpoint chart bookkeeping for the ordinary and transported adjacent
  analytic elements.

mathematical input proved here:
  hzero_plus and hzero_minus, local zero-height pairings against Tlocal.  The
  proof derives AdjEdge = OrdEdge by transitivity of those two fields, without
  inserting a source-representation or common-boundary wrapper.
```

The next Lean target is therefore not a finite-height side theorem.  It is the
local transfer theorem that produces the current adjacent `(4.12)` analytic
element at the flat endpoint and proves the source-side zero representation
above.
A helper that assumes the equality above, assumes zero-height equality, or
mentions an already-built `Hdiff`/`Wadj` would be a wrapper and should not be
added.

#### Proof-local side-limit algebra

The former finite-height Wick-test shortcut is retired, but the side-height
boundary-value calculation below is active proof-local algebra for producing
`hzero_plus` and `hzero_minus`.  It should not be exported as a public theorem
surface that assumes the hard transfers; it must be proved inside the Stage-A
flat crossing from the ordinary `(4.1)` endpoint, the raw transported adjacent
`(4.12)` chain, and `(4.14)` boundary covariance.

```lean
-- All objects are proof-local inside
-- BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45.
let D : BHW.OS45Figure24SourceCutoffData P :=
  Classical.choice (BHW.exists_os45Figure24SourceCutoffData P)
let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
let Fplus0 : BHW.OS45FlatCommonChartReal d n -> Complex := fun x =>
  BHW.os45FlatCommonChartBranch d n OS lgc
    (1 : Equiv.Perm (Fin n)) (SCV.realEmbed x)
let Fminus0 : BHW.OS45FlatCommonChartReal d n -> Complex := fun x =>
  BHW.os45FlatCommonChartBranch d n OS lgc
    (P.τ.symm * (1 : Equiv.Perm (Fin n))) (SCV.realEmbed x)
let Jflat : Complex := (BHW.os45CommonEdgeFlatJacobianAbs n : Complex)

obtain <hCone_open, hCone_conv, hCone_zero, hCone_scale, hCone_nonempty> :=
  BHW.os45FlatCommonChartCone_eowReady d n
obtain <eta0, heta0> := hCone_nonempty
let Keta : Set (BHW.OS45FlatCommonChartReal d n) := {eta0}
have hKeta_compact : IsCompact Keta := by
  simp [Keta]
have hKeta_nonempty : Keta.Nonempty := by
  exact <eta0, by simp [Keta]>
have hKeta_cone :
    Keta <= BHW.os45FlatCommonChartCone d n := by
  intro eta heta
  simpa [Keta] using heta0

let BranchPlusSide :
    Real -> BHW.OS45FlatCommonChartReal d n -> Complex := fun eps eta =>
  integral fun x : BHW.OS45FlatCommonChartReal d n =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
      (fun a => (x a : Complex) + (eps : Complex) * (eta a : Complex) * Complex.I)
      * phi x

let BranchMinusSide :
    Real -> BHW.OS45FlatCommonChartReal d n -> Complex := fun eps eta =>
  integral fun x : BHW.OS45FlatCommonChartReal d n =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      (fun a => (x a : Complex) - (eps : Complex) * (eta a : Complex) * Complex.I)
      * phi x

let SourcePlusSide :
    Real -> BHW.OS45FlatCommonChartReal d n -> Complex := fun eps eta =>
  Jflat *
    integral fun u : NPointDomain d n =>
      bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta phi).1 :
            SchwartzNPoint d n) : NPointDomain d n -> Complex) u)

let SourceMinusSide :
    Real -> BHW.OS45FlatCommonChartReal d n -> Complex := fun eps eta =>
  Jflat *
    integral fun u : NPointDomain d n =>
      bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
        ((((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta phi).1 :
            SchwartzNPoint d n) : NPointDomain d n -> Complex) u)
```

The zero-height limits of the two branch-side families are ordinary
continuity facts, not Schwinger identities:

```lean
have hBranchPlus_zero :
    TendstoUniformlyOn BranchPlusSide
      (fun _ => integral fun x => Fplus0 x * phi x)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
  -- with the checked plus flat domain membership.
  exact flat_plus_side_integral_tends_to_zero_height
    hKeta_compact hKeta_cone phi hphi_compact hphiE

have hBranchMinus_zero :
    TendstoUniformlyOn BranchMinusSide
      (fun _ => integral fun x => Fminus0 x * phi x)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
  -- with the checked minus flat domain membership.
  exact flat_minus_side_integral_tends_to_zero_height
    hKeta_compact hKeta_cone phi hphi_compact hphiE
```

The common source limit is checked in source variables.  In the flat chart the
limit is multiplied by the source-to-flat Jacobian
`BHW.os45CommonEdgeFlatJacobianAbs n`; this normalization matches the checked
common-edge change-of-variables lemmas such as
`BHW.os45FlatCommonChart_ordinaryCommonBoundary_integral_eq_sourcePullback`.

```lean
have hsource_limits :=
  D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
    OS lgc Keta hKeta_compact hKeta_cone phi hphi_compact hphiE

have hSourcePlus_common :
    TendstoUniformlyOn SourcePlusSide
      (fun _ =>
        Jflat * OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- `hsource_limits.1`, scaled by the source-to-flat Jacobian.
  have hscale : UniformContinuous (fun c : Complex => Jflat * c) := by
    exact uniformContinuous_mul_left Jflat
  simpa [SourcePlusSide] using
    hscale.comp_tendstoUniformlyOn hsource_limits.1

have hSourceMinus_common :
    TendstoUniformlyOn SourceMinusSide
      (fun _ =>
        Jflat * OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- `hsource_limits.2.2.2`, scaled by the source-to-flat Jacobian.
  have hscale : UniformContinuous (fun c : Complex => Jflat * c) := by
    exact uniformContinuous_mul_left Jflat
  simpa [SourceMinusSide] using
    hscale.comp_tendstoUniformlyOn hsource_limits.2.2.2
```

The two hard transfer congruences below are the proof bodies to implement.
They are not assumptions for a public theorem.  They must be proved from the
ordinary `(4.1)` chain, the transported genuine adjacent `(4.12)` chain, and
their endpoint-centered trace formulas.

The correct finite-height statement is asymptotic, not eventual equality.  The
branch-side family and the source-side family approach the same boundary value
as the side height tends to zero.  A proof may specialize to eventual equality
only if a checked endpoint formula gives that equality after the common-edge
change of variables.  The generic target is:

```lean
have hPlus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- Establish the ordinary `(4.1)/(4.14)` branch/source transfer in place.
  -- Build the eventual ordinary side pullback by the checked signed
  -- source-side normal form, prove the ordinary moving side-height
  -- boundary-value limit against the selected `(4.1)` boundary CLM, compare
  -- that limit with the checked source-side Schwinger limit, and lift the
  -- fixed-direction statement to the singleton `Keta`.
  -- The expanded Lean-pseudocode body is the "Exact Side-Height `(4.14)`
  -- Transfer Leaf" below; there is no theorem call to insert here.

have hMinus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- Establish the transported raw-adjacent `(4.12)/(4.14)` branch/source
  -- transfer.  Start from `OmegaSeed412/BSeed412`, transport that analytic
  -- element through the adjacent one-branch chain, rewrite to the terminal
  -- flat endpoint only after the chain supplies the overlap equality, then
  -- apply the same moving boundary-value calculation on the minus sheet.
  -- The deterministic `extendF o permAct` expression is endpoint
  -- bookkeeping here, never upstream seed data.
```

The final common-limit facts are then pure filter algebra:

```lean
have hPlus_trace_transfer :
    TendstoUniformlyOn BranchPlusSide
      (fun _ =>
        Jflat * OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- `hPlus_asymptotic` plus the checked source-side common limit.
  exact SCV.tendstoUniformlyOn_of_sub_tendstoUniformlyOn_zero
    hPlus_asymptotic hSourcePlus_common

have hMinus_trace_transfer :
    TendstoUniformlyOn BranchMinusSide
      (fun _ =>
        Jflat * OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- `hMinus_asymptotic` plus the checked source-side common limit.
  exact SCV.tendstoUniformlyOn_of_sub_tendstoUniformlyOn_zero
    hMinus_asymptotic hSourceMinus_common
```

Then the compact-test equality is a direct neutral filter consequence:

```lean
have h414_integrals_phi :
    (integral fun x => Fminus0 x * phi x) =
      integral fun x => Fplus0 x * phi x := by
  exact
    (SCV.eq_zeroHeight_of_common_sideLimit
      (l := nhdsWithin (0 : Real) (Set.Ioi 0))
      hKeta_nonempty
      hBranchMinus_zero hBranchPlus_zero
      hMinus_trace_transfer hPlus_trace_transfer)
```

This reduces the live flat gap to proving the two named asymptotic
trace-transfer blocks, with the second one carrying the genuine `(4.12)`
provenance.  Any Lean lemma that simply takes `hPlus_trace_transfer`,
`hMinus_trace_transfer`, `h414_integrals_phi`, `hPlus_asymptotic`, or
`hMinus_asymptotic` as an input has not closed the mathematical gap.

The neutral filter helper above is acceptable support if it is not already in
Mathlib/SCV.  It has no OS content and should have the exact mathematical
statement:

```lean
theorem SCV.tendstoUniformlyOn_of_sub_tendstoUniformlyOn_zero
    {ι α : Type*} {l : Filter ι} {K : Set α}
    {F G : ι -> α -> Complex} {c : Complex}
    (hsub :
      TendstoUniformlyOn
        (fun eps eta => F eps eta - G eps eta)
        (fun _ : α => 0) l K)
    (hG : TendstoUniformlyOn G (fun _ : α => c) l K) :
    TendstoUniformlyOn F (fun _ : α => c) l K := by
  -- use `F = (F - G) + G` and uniform convergence under addition.
```

#### Trace-transfer theorem shapes

Correction, 2026-05-16: the side-limit-to-Schwinger shape is **not** the
active theorem target.  It would identify the zero-height flat real common-edge
pairings individually with the Wick-section Schwinger functional, which is the
Schwinger-CLM shortcut rejected in the main theorem-2 audit.  The checked
source Wick-section pairings normalize the `(4.1)` and `(4.12)` analytic
elements on the source side; they do not by themselves identify the
zero-height real common-edge distribution with `OS.S`.

The active target inside the flat block is the direct common-boundary compact
test equality:

```lean
let OrdEdge : Complex :=
  ∫ x : BHW.OS45FlatCommonChartReal d n,
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex)) * phi x

let AdjEdge : Complex :=
  ∫ x : BHW.OS45FlatCommonChartReal d n,
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      (fun a => (x a : Complex)) * phi x

have h414_integrals_phi : AdjEdge = OrdEdge := by
  -- proof-local zero-height pairings from the two side-height branch/source
  -- transfers plus the checked source-side common limit; expanded below
```

Its proof must **not** follow the retired two-pullback-to-Wick skeleton.  The
two individual targets

```lean
OrdEdge = (BHW.os45CommonEdgeFlatJacobianAbs n : Complex) *
  ∫ u, bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
    (D.toSchwartzNPointCLM 1 phi u)

AdjEdge = (BHW.os45CommonEdgeFlatJacobianAbs n : Complex) *
  ∫ u, bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
    (D.toSchwartzNPointCLM 1 phi u)
```

would again identify a zero-height flat real common-boundary pairing with a
Wick/source anchor if asserted directly from the checked source Wick equality
or installed as a standalone assumption.  That direct shortcut is not allowed.
The only admissible way to obtain such equalities is proof-locally: derive the
branch-side/source-side asymptotic transfers from `(4.14)`, use the checked
source-side common limit, and identify the zero-height branch limits by
`SCV.eq_zeroHeight_of_common_sideLimit` or uniqueness of limits.  Deep
Research interaction
`v1_ChdtVVlJYXQzOEJybTBuc0VQZ2UyRDJROBIXbVVZSWF0MzhCcm0wbnNFUGdlMkQyUTg`
completed on 2026-05-16 and agrees with the local audit: the strict OS-I
target is Option B, a common-boundary distribution producing
`AdjEdge = OrdEdge`; in the Lean proof this is produced from the local
zero-height pairings `hzero_plus` and `hzero_minus`.  Individual zero-height
normalization to the Wick or Schwinger anchor is category-confused and circular
when used as a primitive shortcut; as a derived boundary-limit consequence it
is just the expanded proof of the common-boundary equality.

The active proof-local target is therefore:

```lean
have hzero_plus : OrdEdge = Tlocal phi := by
  -- ordinary plus-side fixed-test selection, moving-test perturbation,
  -- endpoint DCT, and common source limit.

have hzero_minus : AdjEdge = Tlocal phi := by
  -- raw-adjacent minus-side fixed-test selection, moving-test perturbation,
  -- endpoint DCT, and common source limit.
```

The compact-test equality is then just:

```lean
have h414_integrals_phi : AdjEdge = OrdEdge := by
  exact hzero_minus.trans hzero_plus.symm
```

The checked common-edge change-of-variables lemmas remain useful only as
coordinate bookkeeping after the side-height branch/source transfers have
selected the zero-height limit:
`BHW.os45FlatCommonChart_ordinaryCommonBoundary_integral_eq_sourcePullback`
and
`BHW.os45FlatCommonChart_adjacentCommonBoundary_integral_eq_sourcePullback`
rewrite flat integrals into `os45PulledRealBranch` variables.  They do not
prove that either pulled branch is the Wick source branch.

The checked source equality
`BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick` is also still
load-bearing, but only as a Wick-seed equality after the genuine adjacent
`(4.12)` element has been transported to an actual holomorphic function
`Badj412` on the same connected chart as the ordinary branch.  It is not a
zero-height flat common-boundary theorem and must not be used as a substitute
for `hzero_plus`/`hzero_minus`.

The ordinary zero-height pairing then represents
`Tlocal := BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P` by the checked
ordinary-edge representation theorem, and the adjacent zero-height pairing
represents the same `Tlocal` by `h414_integrals_phi`.  These are exactly the
inputs of
`BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`.

The older side-to-Schwinger skeleton is retired as a shortcut, not as
boundary-value technology.  Do not add public theorems that merely assume
`hPlus_asymptotic`, `hMinus_asymptotic`, or named side-to-Schwinger shortcut
theorems.  If fixed-direction branch/source transfer names are used in Lean,
they must be private/proof-local support lemmas whose proofs unfold the OS-I
`(4.1)/(4.12)/(4.14)` boundary-value argument below.

Proof-local boundary-limit algebra follows.  The two asymptotic blocks are
valid only as the route to the common-boundary equality `AdjEdge = OrdEdge`;
they are not independent zero-height flat-edge-to-Schwinger normalizations.

The retired side-limit calculation had specialized the cone-direction set to

```lean
let Keta : Set (BHW.OS45FlatCommonChartReal d n) := {eta0}
```

so the first theorem to prove is **fixed-direction**, not a new compact-family
boundary-value theorem.  The `TendstoUniformlyOn` target on `Keta` below is
only the shape expected by the checked common-side-limit helper.  It should be
obtained from a fixed-direction statement by a neutral singleton bridge:

```lean
have hPlus_asymptotic_eta0 :
    Tendsto
      (fun eps => BranchPlusSide eps eta0 - SourcePlusSide eps eta0)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (0 : Complex)) := by
  -- Inline the fixed-direction ordinary transfer:
  -- side-domain membership and the checked source-side pullback identify the
  -- branch family with the ordinary endpoint branch evaluated on the moving
  -- `D.toSideZeroDiagonalCLM` tests; the ordinary `(4.1)` boundary-value
  -- theorem plus `(4.14)` source normalization gives the same limit as the
  -- checked source-side family.  The resulting subtraction tends to zero.
  -- This is expanded in the "Exact Side-Height `(4.14)` Transfer Leaf"
  -- section below.

have hPlus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  simpa [Keta] using
    (SCV.tendstoUniformlyOn_singleton_iff_tendsto
      (F := fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
      (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (p := nhdsWithin (0 : Real) (Set.Ioi 0))
      (x := eta0)).2 hPlus_asymptotic_eta0
```

and similarly for the adjacent/minus side.  This uses Mathlib's
`SCV.tendstoUniformlyOn_singleton_iff_tendsto` directly; do not add a local
singleton wrapper.

The fixed-direction branch proof should therefore be transcribed with the
following dependency order.  The support inputs are checked; the middle step is
the genuine OS-I work, now pinned to the private Hdiff leaves instead of to
schematic `hWord_fixed`/`hWadj_fixed` wrappers.

```lean
let l := nhdsWithin (0 : Real) (Set.Ioi 0)
let psi0 : ZeroDiagonalSchwartz d n :=
  D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi
let psiepsPlus : Real -> ZeroDiagonalSchwartz d n :=
  fun eps => D.toSideZeroDiagonalCLM
    (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta0 phi
let psiepsMinus : Real -> ZeroDiagonalSchwartz d n :=
  fun eps => D.toSideZeroDiagonalCLM
    (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta0 phi

-- checked support: moving side-cutoff tests converge in Schwartz space
have hpsiPlus_move : Tendsto psiepsPlus l (nhds psi0) := by
  exact
    (D.toSideZeroDiagonalCLM_tendsto_zero
      (1 : Equiv.Perm (Fin n)) (1 : Real) eta0 phi hphi_compact).mono_left
      nhdsWithin_le_nhds

have hpsiMinus_move : Tendsto psiepsMinus l (nhds psi0) := by
  exact
    (D.toSideZeroDiagonalCLM_tendsto_zero
      (1 : Equiv.Perm (Fin n)) (-1 : Real) eta0 phi hphi_compact).mono_left
      nhdsWithin_le_nhds

have hpsiPlus_move_val :
    Tendsto (fun eps => ((psiepsPlus eps).1 : SchwartzNPoint d n))
      l (nhds ((psi0).1 : SchwartzNPoint d n)) := by
  exact (continuous_subtype_val.tendsto psi0).comp hpsiPlus_move

have hpsiMinus_move_val :
    Tendsto (fun eps => ((psiepsMinus eps).1 : SchwartzNPoint d n))
      l (nhds ((psi0).1 : SchwartzNPoint d n)) := by
  exact (continuous_subtype_val.tendsto psi0).comp hpsiMinus_move

-- checked source-side fixed-test leaves: the flat side-height vector is not a
-- raw OS-I direction.  First pull the signed flat branch to the genuine OS45
-- sourceSide path, then select the zero-height Wick endpoint on the local
-- carrier.  Raw OS-I moving leaves may enter only after a separate
-- quarter-turn/half-time ray identity has been proved.
let psi0Flat :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))).symm)
    ((psi0).1 : SchwartzNPoint d n)
let pullFlatToSource :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)))

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
  -- Source-side carrier membership:
  -- `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`.
  -- Exact translated-test pullback:
  -- `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest`.
  -- Boundary selection:
  -- the ordinary one-branch terminal trace first selects the flat boundary
  -- value, then scalar cancellation lands in `Word psi0`; endpoint DCT and
  -- Schwinger normalization are handled by `hOrd_boundary_to_source` and
  -- `hOrd_source_norm`.

have hAdj_sourceSide_fixed :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          FAdj (BHW.os45FlatCommonChartSourceSide
            d n (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta0 u) *
          ((psi0).1 : SchwartzNPoint d n) u)
      l
      (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
  -- Same source-side carrier and scalar-cancellation calculation with `FAdj`.
  -- The retained raw `(4.12)` seed must be transported through `chainAdj`
  -- to select the flat minus boundary value before this leaf lands in
  -- `Wadj psi0`.  Endpoint DCT and adjacent Schwinger normalization are
  -- handled later by `hAdj_boundary_to_source` and `hAdj_source_norm`; the
  -- downstream `extendF o permAct` expression is not seed data.

-- genuine OS-I content: compare branch-side and source-side side-height
-- families.  These are asymptotic statements, not individual zero-height
-- normalizations to a Wick/Schwinger anchor.
have hPlus_asymptotic_eta0 :
    Tendsto
      (fun eps => BranchPlusSide eps eta0 - SourcePlusSide eps eta0)
      l (nhds (0 : Complex)) := by
  -- Pull the plus branch to the ordinary source-side sheet, apply the
  -- moving-test ordinary boundary-value limit, normalize the boundary CLM
  -- by the OS-I `(4.1)/(4.14)` source restriction on
  -- `D.toZeroDiagonalCLM 1 phi`, and subtract the checked source-side limit.
  have hbranch_to_sourceCommon :
      Tendsto (fun eps => BranchPlusSide eps eta0) l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    -- Inline ordinary proof:
    -- (a) use `hBranchPlus_pullback_eventually` to replace the flat branch
    --     by the source-side ordinary `extendF` pairing;
    -- (b) use `hOrd_moving`, obtained from the checked moving-test boundary
    --     theorem, for the moving source tests;
    -- (c) rewrite the selected ordinary boundary CLM by the endpoint
    --     `(4.1)/(4.14)` normalization on `D.toZeroDiagonalCLM 1 phi`.
  have hsource_eta0 :
      Tendsto (fun eps => SourcePlusSide eps eta0) l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    exact (hSourcePlus_common.tendsto hKeta_eta0)
  exact hbranch_to_sourceCommon.sub hsource_eta0 |>.congr'
    (by filter_upwards with eps; ring_nf)

have hMinus_asymptotic_eta0 :
    Tendsto
      (fun eps => BranchMinusSide eps eta0 - SourceMinusSide eps eta0)
      l (nhds (0 : Complex)) := by
  -- Pull the minus branch to the source-side sheet carrying the transported
  -- raw `(4.12)` analytic element, apply the adjacent fixed-test and
  -- moving-test boundary-value calculation, rewrite the endpoint by
  -- `hAdj_terminal_eq_endpoint` only after the raw chain has reached the
  -- terminal chart, and subtract the checked source-side limit.
  have hbranch_to_sourceCommon :
      Tendsto (fun eps => BranchMinusSide eps eta0) l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    -- Inline adjacent proof:
    -- (a) use `hBranchMinus_pullback_eventually` to replace the flat branch
    --     by the source-side terminal adjacent pairing;
    -- (b) transport the raw `OmegaSeed412/BSeed412` boundary CLM through the
    --     adjacent one-branch chain before any endpoint rewrite;
    -- (c) use `hAdj_moving` for the moving source tests;
    -- (d) identify the terminal boundary value with the same source common
    --     limit by the `(4.12)/(4.14)` normalization.
  have hsource_eta0 :
      Tendsto (fun eps => SourceMinusSide eps eta0) l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    exact (hSourceMinus_common.tendsto hKeta_eta0)
  exact hbranch_to_sourceCommon.sub hsource_eta0 |>.congr'
    (by filter_upwards with eps; ring_nf)
```

The branch/source asymptotic proof is meant to remain in this local proof
body.  If Lean needs a split, only neutral coordinate/support pieces may be
exported; a theorem that assumes either branch/source asymptotic transfer
would still be wrapper churn.

#### Proof-Local Common Side-Limit Consequence

After the two fixed-direction asymptotic transfers are proved, specialize the
checked source theorem to the singleton direction, lift the two asymptotics to
`TendstoUniformlyOn` on `Keta`, and apply
`SCV.eq_zeroHeight_of_common_sideLimit`.  The active target is `AdjEdge =
OrdEdge`; there is no separate active theorem asserting `OrdEdge =
FlatSchwinger` or `AdjEdge = FlatSchwinger`.

Ordinary side:

```lean
have hPlus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta =>
        BranchPlusSide eps eta - SourcePlusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- Inputs in scope:
  --   chainOrd : Chain ordinary41
  --   endpointOrd : terminal ordinary chart at the horizontal common edge
  --   D : BHW.OS45Figure24SourceCutoffData P
  --   phi, hphi_compact, hphiE.

  -- 1. Shrink the positive-side filter so every side point
  --
  --      fun a => (x a : Complex) + (eps : Complex) *
  --        (eta a : Complex) * Complex.I
  --
  --    lies in the ordinary flat domain
  --    `BHW.os45FlatCommonChartOmega d n 1` for all
  --    `x in tsupport phi` and `eta in Keta`.
  obtain <r_side, hr_side, hplus_side_mem, hminus_side_mem> :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P)
      (tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex))
      hphi_compact.isCompact hphiE
      Keta hKeta_compact hKeta_cone

  -- 2. Transport the terminal ordinary chart to the endpoint-centered
  --    ordinary common-edge chart.  This is the checked ordinary chain,
  --    ultimately normalized by
  --    `H.ordinaryCommonEdge_metricBallChartInWindow` and
  --    `BHW.os45Figure24Path_endpoint_extendF_eq_ordinaryPulledRealBranch`.
  have hOrd_terminal_eq_extendF :
      Set.EqOn endpointOrd.branch
        (BHW.extendF (bvt_F OS lgc n))
        endpointOrd.carrier := by
    exact chainOrd.terminal_eq_ordinary_global

  -- 3. Re-express the side integral by the ordinary OS-I `(4.1)` boundary
  --    value theorem against the shifted cutoff-pulled source tests.  This is
  --    a convergence statement, not a pointwise finite-height identity:
  have hOrd_bv_eta0 :
      Tendsto
        (fun eps =>
          BranchPlusSide eps eta0 - SourcePlusSide eps eta0)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (0 : Complex)) := by
    have hBranchPlus_to_common :
        Tendsto (fun eps => BranchPlusSide eps eta0)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds
            (Jflat *
              OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) phi))) := by
      -- Ordinary local body, with no exported theorem:
      -- 1. `hplus_sheet`: specialize
      --    `BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually`
      --    to `{eta0}` and the positive side.
      -- 2. `hplus_pullback`: rewrite `BranchPlusSide eps eta0`
      --    eventually by
      --    `BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM`
      --    to
      --    `Jflat * ∫ u, extendF(bvt_F)(sourceSide 1 eps eta0 u) *
      --      (psiPlus eps eta0).1 u`.
      -- 3. `hOrd_fixed_psi0`: select the ordinary source-side quarter-turn
      --    limit for the concrete compact test
      --    `psi0 = D.toZeroDiagonalCLM 1 phi`, using ExtendedTube
      --    membership, zero-height endpoint DCT, and ordinary endpoint trace
      --    normalization.  Do not unflatten `eta0` into a raw cone direction.
      -- 4. `hOrd_moving`: apply the checked compact-support moving-test
      --    perturbation to replace `psi0` by `psiPlus eps eta0`.
      -- 5. `hOrd_boundary_to_source` and `hOrd_source_norm`: identify the
      --    selected boundary functional with the source Wick pairing and then
      --    with `OS.S n (D.toZeroDiagonalCLM 1 phi)`.
      -- 6. Combine `hplus_pullback`, the resulting branch limit, and
      --    `hSourcePlus_common.tendsto hKeta_eta0`, then subtract.
    have hSourcePlus_to_common :
        Tendsto (fun eps => SourcePlusSide eps eta0)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds
            (Jflat *
              OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) phi))) := by
      exact (hSourcePlus_common.tendsto hKeta_eta0)
    exact hBranchPlus_to_common.sub hSourcePlus_to_common |>.congr'
      (by filter_upwards with eps; ring_nf)

  have hOrd_bv :
      TendstoUniformlyOn
        (fun eps eta =>
          BranchPlusSide eps eta - SourcePlusSide eps eta)
        (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
    simpa [Keta] using
      (SCV.tendstoUniformlyOn_singleton_iff_tendsto
        (F := fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
        (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
        (p := nhdsWithin (0 : Real) (Set.Ioi 0))
        (x := eta0)).2 hOrd_bv_eta0

  exact hOrd_bv
```

Adjacent side:

```lean
have hMinus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta =>
        BranchMinusSide eps eta - SourceMinusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- Inputs in scope:
  --   chainAdj : Chain adjacent412
  --   endpointAdj : terminal adjacent chart at the horizontal common edge
  --   seed provenance: Cseed/Bseed is the shrunk genuine `(4.12)` seed,
  --   not downstream deterministic adjacent data.

  -- 1. Shrink the positive-side filter so every negative-side point
  --
  --      fun a => (x a : Complex) - (eps : Complex) *
  --        (eta a : Complex) * Complex.I
  --
  --    lies in the adjacent flat domain
  --    `BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)`.
  obtain <r_side, hr_side, hplus_side_mem, hminus_side_mem> :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P)
      (tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex))
      hphi_compact.isCompact hphiE
      Keta hKeta_compact hKeta_cone

  -- 2. Transport the genuine `(4.12)` analytic element to the endpoint
  --    adjacent common-edge chart.  The endpoint chart may be represented by
  --    `z => BHW.extendF (bvt_F OS lgc n) (BHW.permAct P.τ z)`, but only
  --    after the chain has proved equality with the branch transported from
  --    Cseed/Bseed.
  have hAdj_terminal_eq_endpoint :
      Set.EqOn endpointAdj.branch
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z))
        endpointAdj.carrier := by
    exact chainAdj.terminal_eq_transported_adjacent_endpoint

  have hAdj_endpoint_trace :
      endpointAdj.branch endpointAdj.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) endpointSource)) := by
    -- endpoint-centered bookkeeping only:
    -- `BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch`.
    exact endpointAdj.trace

  -- 3. Apply the OS-I `(4.12)` boundary-value convergence for the transported
  --    adjacent analytic element against the signed cutoff-pulled source
  --    tests.  This is the hard `(4.12)/(4.14)` transfer.  It is not the
  --    checked downstream adjacent endpoint formula by itself.
  have hAdj_bv_eta0 :
      Tendsto
        (fun eps =>
          BranchMinusSide eps eta0 - SourceMinusSide eps eta0)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (0 : Complex)) := by
    -- The fixed-direction theorem uses the transported genuine `(4.12)`
    -- analytic element.  It may rewrite the endpoint chart by
    -- `hAdj_terminal_eq_endpoint` only after the chain has transported the
    -- raw seed; it must not use the downstream deterministic branch as the
    -- initial datum.
    have hBranchMinus_to_common :
        Tendsto (fun eps => BranchMinusSide eps eta0)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds
            (Jflat *
              OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) phi))) := by
      -- Raw-adjacent local body, with no exported theorem:
      -- 1. `hminus_sheet`: specialize the checked side sheet packet to
      --    `P.τ.symm * 1` and the negative side.
      -- 2. `hminus_pullback`: use the signed source-side pullback with
      --    `σ = P.τ.symm * 1`, `ρperm = 1`, and `sgn = -1`, then rewrite to
      --    `Badj_terminal` only through the retained raw `(4.12)` terminal
      --    endpoint equality.
      -- 3. `hAdj_fixed_psi0`: select the adjacent source-side quarter-turn
      --    limit from the transported `OmegaSeed412/BSeed412` endpoint.  This
      --    is before the deterministic `extendF o permAct` endpoint rewrite
      --    and does not use `etaAdjRaw := -unflatten eta0`.
      -- 4. `hAdj_moving`: apply the checked compact-support moving-test
      --    perturbation to replace `psi0` by `psiMinus eps eta0`.
      -- 5. `hAdj_boundary_to_source` and `hAdj_source_norm`: transport the
      --    raw endpoint trace, use the adjacent Wick/source normalization,
      --    and identify the same value
      --    `OS.S n (D.toZeroDiagonalCLM 1 phi)`.
      -- 6. Combine the minus pullback, the resulting branch limit, and
      --    `hSourceMinus_common.tendsto hKeta_eta0`, then subtract.
    have hSourceMinus_to_common :
        Tendsto (fun eps => SourceMinusSide eps eta0)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds
            (Jflat *
              OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) phi))) := by
      exact (hSourceMinus_common.tendsto hKeta_eta0)
    exact hBranchMinus_to_common.sub hSourceMinus_to_common |>.congr'
      (by filter_upwards with eps; ring_nf)

  have hAdj_bv :
      TendstoUniformlyOn
        (fun eps eta =>
          BranchMinusSide eps eta - SourceMinusSide eps eta)
        (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
    simpa [Keta] using
      (SCV.tendstoUniformlyOn_singleton_iff_tendsto
        (F := fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
        (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
        (p := nhdsWithin (0 : Real) (Set.Ioi 0))
        (x := eta0)).2 hAdj_bv_eta0

  exact hAdj_bv
```

In the corrected route, the two fixed-direction branch/source asymptotic
proof bodies above are the OS-I work to implement inside this local flat
block.  They do not normalize zero-height edges directly to a Wick/Schwinger
anchor; they compare side-height branch integrals to side-height source
integrals.  The checked source common limit and
`SCV.eq_zeroHeight_of_common_sideLimit` then produce the common-boundary
equality.  Do not surface these asymptotic statements as public hypotheses.

Lean readiness test for either transfer lemma:

```lean
-- acceptable new support
have hsupport :=
  D.toSideZeroDiagonalCLM_tsupport_subset_image_eventually
    hUlocal_open Keta hKeta_compact phi hphi_compact hphiUlocal

have hsource :=
  D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
    OS lgc Keta hKeta_compact hKeta_cone phi hphi_compact
    (hphiUlocal.trans hE_sub)

-- not acceptable as a theorem hypothesis
--   the plus-side branch/source asymptotic transfer
--   the minus-side branch/source asymptotic transfer
--   either fixed-direction singleton version of those transfers
```

The proof must create the displayed asymptotic statement from the OS-I branch
chain and endpoint trace fields.  If a proposed Lean statement merely consumes
one of those asymptotic statements, it has not advanced the proof.

#### Boundary-value API audit

The existing OS-II boundary-value theorem

```lean
BHW.bvt_boundary_values
```

is useful but not sufficient by itself.  It gives raywise convergence of
forward-tube side integrals to the selected Wightman boundary functional
`bvt_W OS lgc n f` for a fixed source test `f` and fixed forward-cone
direction.  It does not identify that boundary functional with the Schwinger
functional on the Figure-2-4 local source tests, and it does not transport the
genuine adjacent `(4.12)` analytic element.

Therefore the following shortcut is circular and must not be used:

```lean
-- invalid as a closure step:
-- use `bvt_boundary_values` to show the branch-side real-edge pairing is
-- already the same zero-diagonal Schwinger functional, then feed that as
-- `h414_integrals`.
```

The missing OS-I content is precisely the local normalization that compares the
ordinary `(4.1)` and transported adjacent `(4.12)` branch-side boundary traces
with the checked source-side Schwinger limits on the cutoff-pulled tests.  A
valid proof may use `bvt_boundary_values` as one analytic ingredient, but only
after it supplies the OS-I identity-theorem/edge-transfer step that connects
the resulting `bvt_W` boundary value to the Schwinger-side source pairing in
this Figure-2-4 window.

The moving-test part of that analytic ingredient is checked in tube coordinates
as `SCV.tube_boundaryValueData_moving_of_fixed`.  Use it only after the boundary
functional has already been selected; in OS45 flat common-chart coordinates,
use the compact-support perturbation estimate described below.  For a raw tube
ray that has already been produced by the OS45 quarter-turn half-time geometry,
the specialized theorem is checked as `bvt_boundary_values_moving` and can be
written directly as:

```lean
let Word : SchwartzNPoint d n ->L[Complex] Complex :=
  -- the existing `bvt_W OS lgc n` as a continuous complex-linear functional
  bvtW_as_CLM OS lgc n

have hmoving_forward :
    Tendsto
      (fun eps : Real =>
        integral fun x : NPointDomain d n =>
          bvt_F OS lgc n
            (fun k mu => (x k mu : Complex) +
              (eps : Complex) * (etaHalfRaw k mu : Complex) * Complex.I) *
          (((psiepsPlus eps eta0).1 : SchwartzNPoint d n) x))
      l (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
  exact
    bvt_boundary_values_moving
      (d := d) OS lgc n etaHalfRaw hηHalfRaw
      (fun eps : Real => eps) h_eps_to_edge
      hpsiPlus_move_val
```

This pseudo-code names local proof facts, not new public theorem surfaces and
must not be fed by `BHW.unflattenCfgReal n d eta0`.  The adjacent side uses
the same theorem only after the raw `(4.12)` analytic
element has been transported to the endpoint-centered tube chart and its
selected boundary CLM is known.  If the proof is still in a cutoff local chart
rather than a literal tube-domain chart, use the local distributional EOW
family (`SCV.sliceCLM_family_from_distributionalBoundary_of_cutoffSupport` and
`SCV.tendsto_mollified_boundary_of_clm`) before applying the ambient moving-test
logic.

The local support part of the two boundary-value lemmas is checked.  When
`tsupport phi` is contained in the flattened image of the selected source
window `Ulocal`, the proof may invoke:

```lean
have hside_support_Ulocal :
    ∀ᶠ eps in nhdsWithin (0 : Real) (Set.Ioi 0), ∀ eta ∈ Keta,
        tsupport (((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta phi).1 :
            SchwartzNPoint d n) : NPointDomain d n -> Complex) <= Ulocal /\
        tsupport (((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta phi).1 :
            SchwartzNPoint d n) : NPointDomain d n -> Complex) <= Ulocal := by
  exact D.toSideZeroDiagonalCLM_tsupport_subset_image_eventually
    hUlocal_open Keta hKeta_compact phi hphi_compact hphiUlocal
```

This means the side-height proof does not re-establish source-window support
for moving tests.  The actual boundary-value convergence of the ordinary and
transported adjacent analytic elements is supplied by the exact local
side-height transfer transcript below: `hPlus_asymptotic_eta0` uses the ordinary
`(4.1)` chain and `hMinus_asymptotic_eta0` uses the transported raw `(4.12)`
chain.  Both are proof-local bodies, not public assumptions.

Once `hzero_plus` and `hzero_minus` are in hand, the flat crossing seed is
exactly the checked bridge call:

```lean
obtain <hE_open, hE_sub, Tlocal, hzero_plus, hzero_minus> :=
  hflat_zero_height_pairings hUlocal_open hUlocal_sub u0 hu0

obtain <Wflat, hWflat_open, hWflat_pre, hzedgeWflat,
    hWflat_sub, hWflat_eq> :=
  BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
    (d := d) hd OS lgc (P := P)
    hE_open hE_sub ys hys_mem hys_li (e u0) <u0, hu0, rfl>
    Tlocal hzero_plus hzero_minus
```

### `circuit_gallery_glue`

The `hadj412` circuit is a finite gallery with four typed blocks:

```text
raw seed block:
  OmegaSeed412/BSeed412 at zadj

adjacent corridor:
  zadj -> adjLift0 -> adjLift1 -> padj,
  all inside ExtendedTube inter permutedExtendedTubeSector P.τ

flat crossover:
  padj -> pord,
  seed supplied by the local zero-height bridge above

ordinary return:
  pord -> zord,
  ordinary branch equal to OrdGlobal on ExtendedTube
```

The fold keeps all carriers as metric balls and all branches holomorphic:

```lean
have circuit_gallery_glue :
    exists (m : Nat)
      (C : Fin (m + 1) -> Set (Fin n -> Fin (d + 1) -> Complex))
      (B : Fin (m + 1) ->
        (Fin n -> Fin (d + 1) -> Complex) -> Complex),
      C 0 = Cseed412 /\
      B 0 = BSeed412Restricted /\
      C (Fin.last m) = Cadj0 /\
      B (Fin.last m) = BAdj0 /\
      (forall j, IsOpen (C j)) /\
      (forall j, exists p r, 0 < r /\ C j = Metric.ball p r) /\
      (forall j, DifferentiableOn Complex (B j) (C j)) /\
      (forall j, C j <= H.OmegaJ) /\
      (forall i j, (C i \cap C j).Nonempty ->
        exists W, IsOpen W /\ W.Nonempty /\
          W <= C i \cap C j /\ Set.EqOn (B i) (B j) W) /\
      Set.EqOn BAdj0 BSeed412 Wseed412 := by
  -- 1. Use OS412SeedWindow_metricBallChartInWindow for the raw seed.
  -- 2. For each checked JoinedIn corridor, call the checked carrier helper
  --    `BHW.initialSectorOverlap_connectedNeighborhood_of_joinedIn`;
  --    endpoint-centered metric balls are obtained by
  --    `BHW.initialSectorOverlap_endpointMetricBall_of_joinedIn` and
  --    `SCV.exists_metric_ball_subset_inter_of_mem_open`.
  -- 3. Attach ordinary or adjacent local transfer provenance to each endpoint
  --    ball.  The carrier construction is checked; the analytic-element
  --    transfer is the local case split transcribed in `hgrid`, not a new
  --    wrapper packet.
  -- 4. At the unique flat block, call
  --    the proof-local flat zero-height pairing block and then the checked
  --    ambient local zero-height bridge.
  -- 5. Build pair seeds for every nonempty carrier overlap:
  --    ordinary overlaps use OrdGlobal;
  --    adjacent overlaps use adjacent_sector_seed_transport;
  --    flat two-sheet overlaps use Wflat from the bridge.
  -- 6. Apply
  --    SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds.
  -- 7. Glue with SCV.glued_iUnion and restrict to a metric ball around zord.
```

The output of `circuit_gallery_glue` is then unpacked as `hadj412`:

```lean
let OmegaAdj0 := Cadj0
let BAdj0 := BAdj0

have hBAdj0_seed :
    exists Wseed, IsOpen Wseed /\ Wseed.Nonempty /\
      Wseed <= OmegaAdj0 \cap OmegaSeed412 /\
      Set.EqOn BAdj0 BSeed412 Wseed := by
  exact circuit_gallery_glue.seed_eq

have hBAdj0_wick_trace :
    BAdj0 zord =
      bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  -- endpoint-centered trace at zord after the final ordinary-return chart,
  -- transported through the glued circuit equality
  exact circuit_gallery_glue.endpoint_trace
```

After this point the later one-branch chain for `adjacent412` starts from
`OmegaAdj0/BAdj0` at `zord`.  It never starts from
the downstream deterministic adjacent initial data.

## One-Branch Chain Witness

Every selected local element must retain the one-branch chain that produced
its terminal ordinary branch and the one-branch chain that produced its
terminal adjacent branch.  The witness is proof-local.  It should have this
shape, with `kind` equal to either `ordinary41` or `adjacent412`:

```lean
exists (m : Nat)
  (node : Fin (m + 1) -> Fin n -> Fin (d + 1) -> Complex)
  (N : Fin (m + 1) -> Set (Fin n -> Fin (d + 1) -> Complex))
  (B : Fin (m + 1) -> (Fin n -> Fin (d + 1) -> Complex) -> Complex),
  node 0 = p0 /\
  node (Fin.last m) = terminalPoint /\
  (forall j, IsOpen (N j)) /\
  (forall j, IsPreconnected (N j)) /\
  (forall j, node j in N j) /\
  (forall j, exists r : Real, 0 < r /\ N j = Metric.ball (node j) r) /\
  (forall j, DifferentiableOn Complex (B j) (N j)) /\
  (forall j, N j <= sheet kind) /\
  initial_seed kind N B /\
  (forall j : Fin m,
    exists Wj : Set (Fin n -> Fin (d + 1) -> Complex),
      IsOpen Wj /\
      Wj.Nonempty /\
      Wj <= N (Fin.castSucc j) inter N (Fin.succ j) /\
      Set.EqOn (B (Fin.castSucc j)) (B (Fin.succ j)) Wj) /\
  terminalCarrier = N (Fin.last m) /\
  terminalBranch = B (Fin.last m) /\
  terminalCarrier_open : IsOpen terminalCarrier /\
  terminalBranch_continuousOn :
    ContinuousOn terminalBranch terminalCarrier
```

The `initial_seed` field expands as:

```text
ordinary41:
  exists W0, IsOpen W0 and W0.Nonempty and
    W0 <= N 0 inter OmegaOrd0 and Set.EqOn (B 0) BOrd0 W0

adjacent412:
  exists W0, IsOpen W0 and W0.Nonempty and
    W0 <= N 0 inter OmegaAdj0 and Set.EqOn (B 0) BAdj0 W0
```

The terminal chart should also be retargetable to any observed overlap point
`z0` in its carrier: choose a small metric ball around `z0` inside the
terminal carrier, restrict the branch to that ball, and append that restricted
chart as the first or last chart of the comparison gallery.

## Finite Chain Assembly Along The Active Path

The one-branch producer is a reachability proof along the chosen Figure-2-4
path, not a precomputed chain packet.  Do not overload the ordinary path and
the raw adjacent seed path.  In the direct source-current producer there are
two active paths:

```lean
let gammaOrd : unitInterval -> Fin n -> Fin (d + 1) -> Complex :=
  BHW.os45Figure24IdentityPath (d := d) (n := n) x

let gammaAdjSeed : unitInterval -> Fin n -> Fin (d + 1) -> Complex :=
  fun t => BHW.permAct (d := d) P.τ (gammaOrd t)

let gammaOf : BranchKind -> unitInterval -> Fin n -> Fin (d + 1) -> Complex
  | BranchKind.ordinary41 => gammaOrd
  | BranchKind.adjacent412Source => gammaAdjSeed
```

This disambiguation is load-bearing.  The raw `(4.12)` seed window contains
`gammaAdjSeed 0`, not `gammaOrd 0`; the checked obstruction
`H.ordinaryWick_not_mem_OS412SeedWindow` forbids putting `gammaOrd 0` directly
in that raw seed window.  The later `hadj412`/Wick-trace circuit is the
separate return-to-`gammaOrd 0` construction.  It must not be used as an input
to the source-current selector.

For each branch kind, define the reachable times inside the proof body:

```lean
let Reach (kind : BranchKind) : Set unitInterval := fun t =>
  exists (C : ChainWitness kind (gammaOf kind t)),
    C.starts_from_initial_germ /\
    C.terminalPoint = gammaOf kind t
```

`ChainWitness` may be a private local structure in the downstream Hdiff file,
but only as notation for the existential displayed in the preceding section.
It must not be a public theorem input.  Its fields are filled by the script
below:

1. At `t = 0`, build the initial pointed chart directly:
   ordinary uses `H.ordinaryWick_pointedChartInWindow` with
   `OmegaOrd0/BOrd0`; the source-current adjacent chain starts directly from
   the raw `OmegaSeed412/BSeed412` pointed chart at
   `gammaAdjSeed 0 = BHW.permAct P.τ (gammaOrd 0)`.
   The proof-local `hadj412` circuit is downstream of the source-current
   leaves and must not be required for this initial source-selector chart.
2. For an arbitrary time `t`, use the OS-I local Figure-2-4 chart data at
   `gammaOf kind t` to choose an open interval-neighborhood `It` in `unitInterval`
   such that any two parameters in `It` lie in one of the three local transfer
   cases below.  This is obtained by continuity of `gammaOf kind`, openness of
   the selected sheet/window, and
   `SCV.exists_metric_ball_subset_inter_of_mem_open` after choosing the local
   chart window.
3. If `s in Reach kind` and `s, u in It`, append one local transfer step from
   the terminal chart at `gammaOf kind s` to a chart centered at
   `gammaOf kind u`.  The step
   returns a new `Chart`, a `KindProv kind` for it, and an open nonempty seed
   between the old and new branches.  Appending this data gives
   `u in Reach kind`.
4. Therefore `Reach kind` is open.  Its complement is also open: if
   `t notin Reach kind`, choose the same `It`; any `s in It inter Reach kind`
   would extend from `s` to `t`, contradiction.
5. Since `unitInterval` is preconnected and `0 in Reach kind`, conclude
   `Reach kind = Set.univ` by `IsClopen.eq_univ` applied to the clopen
   reachable set.  Instantiating at the target time gives the required finite
   chain.

Lean-facing skeleton:

```lean
have hReach0_ord : (0 : unitInterval) in Reach BranchKind.ordinary41 := by
  -- construct the initial ordinary pointed chart from
  -- `OS45BHWJostHullData.ordinaryWick_pointedChartInWindow`;
  -- all initial-seed fields are `rfl` against `BOrd0`.

have hReach0_adj_src :
    (0 : unitInterval) in Reach BranchKind.adjacent412Source := by
  -- build the raw `(4.12)` pointed chart directly from
  -- `OS45BHWJostHullData.OS412SeedWindow_pointedChart` at
  -- `gammaAdjSeed 0 = BHW.permAct P.τ (gammaOrd 0)`;
  -- no `hadj412`, no `OmegaAdj0/BAdj0`, and no deterministic endpoint branch.

have hlocal_extend :
    forall kind t,
      exists It : Set unitInterval,
        IsOpen It /\ t in It /\
        forall s u,
          s in It -> u in It ->
          s in Reach kind -> u in Reach kind := by
  intro kind t
  -- Choose the OS-I local Figure-2-4 case at `gammaOf kind t`, shrink to a
  -- metric chart window, and call the matching local transfer case below.
  -- The transfer is symmetric inside the selected window because both
  -- directions are restrictions of the same local analytic element or of the
  -- same flat EOW seed.

have hReach_univ_of_initial
    (kind : BranchKind) (hReach0 : (0 : unitInterval) in Reach kind) :
    Reach kind = Set.univ := by
  have hReach_open : IsOpen (Reach kind) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    rcases hlocal_extend kind t with
      ⟨It, hIt_open, htIt, hIt_extend⟩
    exact ⟨It, hIt_open, htIt, fun u hu => hIt_extend t u htIt hu ht⟩
  have hReach_compl_open : IsOpen ((Reach kind)ᶜ) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    rcases hlocal_extend kind t with
      ⟨It, hIt_open, htIt, hIt_extend⟩
    refine ⟨It, hIt_open, htIt, ?_⟩
    intro u hu huReach
    exact ht (hIt_extend u t hu htIt huReach)
  have hReach_closed : IsClosed (Reach kind) := by
    simpa using (isClosed_compl_iff.mpr hReach_compl_open)
  have hReach_clopen : IsClopen (Reach kind) :=
    ⟨hReach_closed, hReach_open⟩
  exact
    IsClopen.eq_univ hReach_clopen
      (by exact ⟨(0 : unitInterval), hReach0⟩)
```

The only branch-specific input to this skeleton is `hReach0`, instantiated as
`hReach0_ord` or the raw source-current `hReach0_adj_src`.  The proof of
`hlocal_extend` for these source-current selectors uses only the ordinary and
retained raw-adjacent corridors; the flat plus/minus EOW transfer is not part
of this selector skeleton.  Thus the finite chain exists because the local
OS-I analytic-element transfer covers the chosen corridor, not because Lean is
handed `chainOrd`, `chainAdj`, `Word`, or `Wadj` as assumptions.

Lean support, 2026-05-17: the clopen reachability step above is now checked as
the neutral theorem
`SCV.reachable_eq_univ_of_local_symmetric_extension` in
`OSReconstruction/SCV/ConnectedNeighborhood.lean`.  In the direct Hdiff proof,
instantiate it with `Reach := Reach kind`, `hReach_nonempty` from
`hReach0_ord` or `hReach0_adj_src`, and `hlocal` supplied by the corresponding
ordinary/raw source-current transfer cases below:

```lean
have hlocal_extend_kind :
    ∀ t : unitInterval, ∃ It : Set unitInterval,
      IsOpen It ∧ t ∈ It ∧
        ∀ ⦃s u : unitInterval⦄,
          s ∈ It → u ∈ It → s ∈ Reach kind → u ∈ Reach kind :=
  fun t => hlocal_extend kind t

have hReach_univ :
    Reach kind = Set.univ :=
  SCV.reachable_eq_univ_of_local_symmetric_extension
    (Reach := Reach kind)
    (by exact ⟨(0 : unitInterval), hReach0⟩)
    hlocal_extend_kind
```

The `hlocal_extend` case split is the same split used later for pointed
overlap seeds, but with source and target both restricted inside one local
window around `gammaOf kind t`:

* Ordinary-sector window:
  `gammaOrd '' It <= BHW.ExtendedTube d n inter H.OmegaJ`.
  Both the old terminal chart and the new chart are compared to `BOrd0` on a
  metric subball, then the returned seed is the checked
  `pointed_seed_edge_of_common_model` specialized to `OrdGlobal`.
* Adjacent-sector source window:
  `gammaAdjSeed '' It <= OmegaSeed412`, or a retained raw restriction of that
  window.  The branch is always `BSeed412`; the endpoint
  `extendF o permAct P.τ` expression is exposed only on terminal
  positive-height support after the appropriate forward-tube membership has
  been proved.  This source-current corridor does not first transport the raw
  seed back to `gammaOrd 0`.
* Flat real-Jost window: this is downstream of the source-current selector.
  The two local sides are the checked
  `BHW.os45FlatCommonChartOmega d n 1` and
  `BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)` with common real edge
  `BHW.os45CommonEdgeFlatCLE d n 1 '' Ulocal`.  It may be used only after the
  side-height proof has produced `hzero_plus` and `hzero_minus`; then the
  transfer seed is exactly
  `flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM`.

## Local Transfer Cases

The finite chain is built from a proof-local transfer theorem along the active
Figure-2-4 path.  For a step from
`p = gammaOf kind s0` to `q = gammaOf kind s1`, first restrict the current
chart to a metric ball inside the incoming sheet and the selected chart
window.  Then produce the successor chart and a nonempty complex-open
transition seed.

For the source-current selector, the transfer has exactly two cases: ordinary
and retained raw-adjacent.  The flat rows below are downstream consumers after
the source-current pairings are already proved.

The local window `It` is always shrunk so that, for `s u ∈ It`, the successor
chart centered at `gammaOf kind u` still contains the previous endpoint
`gammaOf kind s`.  This is the `hpCnext` input in the skeletons below; without
it the seed ball around the previous point would not be available.

The checked carrier fields used by these cases are now fixed:

| Case | Incoming/outgoing domain | Checked data already available | Still mathematical |
| --- | --- | --- | --- |
| Ordinary source-current sector | `BHW.ExtendedTube d n ∩ H.ΩJ` along `gammaOrd` | `H.ordinaryWick_metricBallChartInWindow`, `H.ordinaryCommonEdge_metricBallChartInWindow`, `BHW.os45Figure24Path_endpoint_extendF_eq_ordinaryPulledRealBranch`, ordinary `extendF` holomorphy and invariance | metric-ball shrinking, common-model seed, and identity-theorem propagation |
| Raw-adjacent source-current sector | `OmegaSeed412 = {z | BHW.permAct P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ` along `gammaAdjSeed` | raw `(4.12)` seed window `H.OS412SeedWindow_metricBallChartInWindow`, seed obstruction `H.ordinaryWick_not_mem_OS412SeedWindow`, raw seed holomorphy `H.differentiableOn_OS412SeedBranch`, and the checked `gammaAdjSeed` membership data | common-model propagation against `BSeed412`; `extendF o permAct` is only terminal support-local bookkeeping, not the initial seed |
| Flat real-Jost, downstream after source-current pairings | plus side `BHW.os45FlatCommonChartOmega d n 1`, minus side `BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)`, edge `os45CommonEdgeFlatCLE d n 1 '' Ulocal` | edge-window support, checked ordinary-edge representation, endpoint chart bookkeeping, and `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM` after the two zero-height pairings are proved | `hzero_plus`/`hzero_minus`: the OS-I `(4.14)` local zero-height pairings for the current ordinary `(4.1)` and transported adjacent `(4.12)` elements |
| Flat real-Jost, downstream after `h45_source_eqOn` | same flat chart domains | `BHW.os45FlatCommonChart_zeroHeight_pairings_eq_of_sourceCommonEdge_eqOn` and `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn` | the proof-local source common-edge equality `h45_source_eqOn`, produced only after `Badj412` has Wick and common-edge traces |

Thus the flat case has two layers.  The first layer starts only after the
ordinary/raw source-current corridors have proved the two compact-test
zero-height pairings; it is not used inside those corridors.  The downstream checked
bridge consumes `h45_source_eqOn` and returns an ambient EOW seed after the
Wick-seed identity theorem has already produced that equality.  The upstream
transfer cannot call the downstream bridge with `h45_source_eqOn` as a
hypothesis and then claim the transfer is done.

Each source-current case must instantiate the same proof-local return shape:

```lean
inductive KindProv : BranchKind -> Chart -> Prop
  | ordinary41
      (A : Chart)
      (hsub : A.carrier <= BHW.ExtendedTube d n ∩ H.ΩJ)
      (hmodel : Set.EqOn A.branch BOrd0 A.carrier) :
      KindProv BranchKind.ordinary41 A
  | adjacent412Source
      (A : Chart)
      (hsub : A.carrier <= OmegaSeed412)
      (hmodel : Set.EqOn A.branch BSeed412 A.carrier) :
      KindProv BranchKind.adjacent412Source A

have local_transfer_step :
    forall
      (kind : BranchKind)
      (p q : Fin n -> Fin (d + 1) -> Complex)
      (Aprev : Chart),
      p = Aprev.center ->
      KindProv kind Aprev ->
      transfer_case kind p q ->
        exists (Anext : Chart)
          (Wstep : Set (Fin n -> Fin (d + 1) -> Complex)),
          Anext.center = q /\
          KindProv kind Anext /\
          IsOpen Wstep /\
          Wstep.Nonempty /\
          Wstep <= Aprev.carrier inter Anext.carrier /\
          Set.EqOn Aprev.branch Anext.branch Wstep := by
  -- implemented inline by the two source-current cases below
```

The `KindProv` input and output are proof-local provenance.  They remember
whether the branch is a restriction of `BOrd0` or of the retained raw
`BSeed412`.  They do not contain `Word`, `Wadj`, `Hdiff`, a zero-height
pairing, or a downstream transported `OmegaAdj0/BAdj0` chart.

### Ordinary-Sector Transfer

Incoming and outgoing sheet:

```text
OrdSheet = BHW.ExtendedTube d n
```

The local seed compares both branches by rewriting them to `OrdGlobal` on a
small ball contained in the two carriers:

```lean
exists W, IsOpen W /\ p in W /\
  W <= Cprev.N inter Cnext.N /\
  Set.EqOn Cprev.B Cnext.B W
```

The proof is ordinary identity propagation after both sides are known to equal
`BHW.extendF (bvt_F OS lgc n)` on `W`.

Lean skeleton:

```lean
have hprev_global :
    Set.EqOn Bprev (BHW.extendF (bvt_F OS lgc n)) Cprev := by
  -- from ordinary41 provenance

let Cnext := Metric.ball q rq
let Bnext := BHW.extendF (bvt_F OS lgc n)

have hnext_global :
    Set.EqOn Bnext (BHW.extendF (bvt_F OS lgc n)) Cnext := by
  intro z hz
  rfl

obtain ⟨rho, hrho, hrho_sub⟩ :=
  SCV.exists_metric_ball_subset_inter_of_mem_open
    Cprev_open hpCprev Cnext_open hpCnext

let Wstep := Metric.ball p rho
have hstep_eq : Set.EqOn Bprev Bnext Wstep := by
  intro z hz
  exact (hprev_global (hrho_sub hz).1).trans
    (hnext_global (hrho_sub hz).2).symm
```

### Adjacent-Sector Transfer

Incoming and outgoing sheet:

```text
AdjSourceSheet =
  OmegaSeed412 =
    {z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ
```

For the source-current selector, the initial chart is the raw
`OmegaSeed412/BSeed412` chart at `gammaAdjSeed 0`; a transfer step propagates
that retained section 4.12 element along `gammaAdjSeed`.  It must not replace
the raw seed by the deterministic downstream branch using `extendF` after the
permutation action.

For the later Wick-trace/`hadj412` circuit, a different object
`OmegaAdj0/BAdj0` is built by transporting the same raw seed through the
seed-to-Wick return circuit and proving `gammaOrd 0 ∈ OmegaAdj0`.  That later
object is not an input to `hAdj_side_current`.

The critical non-shortcut for the later `hadj412` Wick-trace circuit is now
explicit.  The checked theorem `BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3`
is the right identity-theorem engine there, but its adjacent input must be the
transported genuine `(4.12)` analytic element:

```lean
-- proof-local, inside BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45
have hadj412_wick_trace :
    forall u, u in Ulocal ->
      Badj412 (fun k => wickRotatePoint (u k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) := by
  -- output of the raw `(4.12)` seed-to-ordinary-Wick transport

have hadj412_common_trace :
    forall u, u in Ulocal ->
      Badj412
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)))) := by
  -- terminal adjacent common-edge chart trace, after transporting the same
  -- genuine `(4.12)` element to the endpoint-centered chart
```

It is invalid to instantiate the same Wick-seed theorem with

```lean
fun z => BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) P.τ z)
```

as the adjacent branch before `hadj412_wick_trace` has been proved.  At
`z = fun k => wickRotatePoint (u k)`, that would require normalizing
`extendF` at `BHW.permAct P.τ z`; this is exactly the missing `(4.12)`
transport and cannot be obtained by `extendF_eq_on_forwardTube`.
The earlier raw-model check of this shortcut is non-certifying under the
current harness rules; the certifying route is the pinned
`deep-research-max-preview-04-2026` Interactions API path recorded in
`agents_chat.md`.  The certified conclusion is that the shortcut is unsound
for the strict route: it assumes the raw adjacent analytic continuation is
already the downstream deterministic permuted continuation.  The corrected
dependency order is raw `(4.12)` seed, OS-I `(4.14)` real-Jost boundary
transfer, finite Figure-2-4 equality transport, horizontal common-edge
evaluation, and only then downstream deterministic endpoint identification.

The local seed has the same shape:

```lean
exists W, IsOpen W /\ p in W /\
  W <= Cprev.N inter Cnext.N /\
  Set.EqOn Cprev.B Cnext.B W
```

but its proof uses the retained section 4.12 chain provenance.

Lean skeleton:

```lean
have hprev_raw :
    Set.EqOn Bprev BSeed412 Cprev := by
  -- from `KindProv.adjacent412Source`; `Cprev <= OmegaSeed412`.

-- Build Cnext by the local BHW/OS-I chart around
-- `q = gammaAdjSeed u` inside `OmegaSeed412`.
let Cnext := Metric.ball q rq
let Bnext := BSeed412

have hnext_raw :
    Set.EqOn Bnext BSeed412 Cnext := by
  intro z hz
  rfl

have hstep_eq :
    exists Wstep, IsOpen Wstep /\ Wstep.Nonempty /\
      Wstep <= Cprev inter Cnext /\
      Set.EqOn Bprev Bnext Wstep := by
  obtain ⟨rho, hrho, hrho_sub⟩ :=
    SCV.exists_metric_ball_subset_inter_of_mem_open
      Cprev_open hpCprev Cnext_open hpCnext
  let Wstep := Metric.ball p rho
  refine ⟨Wstep, Metric.isOpen_ball, ⟨p, Metric.mem_ball_self hrho⟩, ?_, ?_⟩
  · exact hrho_sub
  · intro z hz
    exact (hprev_raw (hrho_sub hz).1).trans
      (hnext_raw (hrho_sub hz).2).symm
```

The overlap-centered `hgrid` argument appears later in the downstream
`branch_seed adjacent412`/`hadj412` case, not in this source-current raw
corridor.  It is not a production theorem or wrapper.  When it is eventually
used, it constructs the finite pointed common-center gallery pair from retained
raw `(4.12)` provenance at the actual overlap point.  A nonempty seed somewhere
in the chart is not enough; the seed consumed by
`pointed_metric_seed_of_restricted_gallery_pair` must contain `z0`.

Once `Badj412`, `hadj412_wick_trace`, and `hadj412_common_trace` are in scope,
the local source common-edge equality is produced by the checked Wick seed
identity theorem, not by a flat bridge wrapper:

The identity theorem is used only at this late point.  It is not a substitute
for analytic continuation of the adjacent `(4.12)` germ through the Figure-2-4
gallery.  Before the call below, both `Ford` and `Badj412` must already be
actual single-valued functions, holomorphic on the same connected open chart
`Ucx`, and the Wick section must lie in `Ucx`.  No simple-connectivity
hypothesis is needed for the identity theorem in that situation; any monodromy
or branch-selection risk has to be discharged earlier by the finite
analytic-element gallery and the upstream flat EOW seed.

```lean
let Ford : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  BHW.extendF (bvt_F OS lgc n)

have hFord_wick :
    forall u, u in Ulocal ->
      Ford (fun k => wickRotatePoint (u k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) := by
  -- ordinary forward-tube normalization at the Wick endpoint

have hFord_common :
    forall u, u in Ulocal ->
      Ford
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  -- checked ordinary common-edge endpoint normalization

obtain <Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem, hUcx_sub> :=
  BHW.os45Figure24_initialSectorOverlap_chartNeighborhood
    (d := d) (n := n) (hd := hd) (P := P)
    hUlocal_compact hUlocal_connected hUlocal_closure

have hBadj_eq_Ford_on_Ucx :
    Set.EqOn Badj412 Ford Ucx := by
  exact
    BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3
      (d := d) hd OS lgc (P := P)
      hUlocal_open hUlocal_nonempty hUlocal_sub
      hUcx_open hUcx_connected hwick_mem
      Ford Badj412
      hFord_holo_on_Ucx hBadj412_holo_on_Ucx
      hFord_wick hadj412_wick_trace

have h45_source_eqOn :
    Set.EqOn Gadj Gord Ulocal := by
  intro u hu
  -- evaluate `hBadj_eq_Ford_on_Ucx` at the horizontal common-edge point,
  -- then rewrite by `hadj412_common_trace` and `hFord_common`.
```

This is the exact point at which the proof creates `h45_source_eqOn`.  The
checked flat source-common-edge bridge may be called only after this block.

### Flat Real-Jost EOW Transfer

Incoming flat side:

```text
FlatPlus = BHW.os45FlatCommonChartOmega d n 1
```

Outgoing flat side:

```text
FlatMinus = BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)
```

Edge:

```text
E <= BHW.os45FlatCommonChartEdgeSet d n P 1
```

The proof order is binding:

1. Choose `Ulocal` and the flat edge image
   `E = BHW.os45CommonEdgeFlatCLE d n 1 '' Ulocal`, proving `E` is open and
   contained in the checked edge set.
2. Prove the OS-I `(4.14)` local zero-height pairings `hzero_plus` and
   `hzero_minus` for the current compact flat test from the ordinary plus and
   raw-adjacent minus branch/source side-height transfers.  This is the
   genuine mathematical step.
3. Derive `∫ Fminus0 * phi = ∫ Fplus0 * phi` directly by transitivity through
   `Tlocal`; do not introduce a source-representation or common-boundary
   wrapper.
5. Feed the resulting local zero-height pairings into the checked ambient
   local EOW bridge
   `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`.

Lean skeleton for the checked bridge call:

```lean
have hUlocal_open : IsOpen Ulocal := by
  -- chosen source window for this flat crossing

have hUlocal_sub : Ulocal <= P.V := by
  -- source window is inside the checked Figure-2-4 patch

let E : Set (BHW.OS45FlatCommonChartReal d n) :=
  BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) '' Ulocal

let Tlocal : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex ->L[Complex] Complex :=
  BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P

let Fplus0 : BHW.OS45FlatCommonChartReal d n -> Complex := fun x =>
  BHW.os45FlatCommonChartBranch d n OS lgc
    (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex))

let Fminus0 : BHW.OS45FlatCommonChartReal d n -> Complex := fun x =>
  BHW.os45FlatCommonChartBranch d n OS lgc
    (P.τ.symm * (1 : Equiv.Perm (Fin n))) (fun a => (x a : Complex))
-- This endpoint expression is legal only after the adjacent chain has
-- transported the raw `(4.12)` seed to the flat endpoint and proved the
-- endpoint trace equality.

have hE_open : IsOpen E := by
  -- image openness from os45CommonEdgeFlatCLE and Ulocal_open

have hE_sub :
    E <= BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n)) := by
  -- BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff and Ulocal <= P.V

have hFplus0_cont : ContinuousOn Fplus0 E := by
  -- differentiability of the ordinary flat branch plus real-edge membership

have hFminus0_cont : ContinuousOn Fminus0 E := by
  -- differentiability of the selected adjacent flat branch plus real-edge
  -- membership

have h414_integrals :
    forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
      HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
      tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fminus0 x * phi x) =
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fplus0 x * phi x) := by
  intro phi hphi_compact hphiE
  let l := nhdsWithin (0 : Real) (Set.Ioi 0)
  let OrdEdge : Complex :=
    integral fun x : BHW.OS45FlatCommonChartReal d n => Fplus0 x * phi x
  let AdjEdge : Complex :=
    integral fun x : BHW.OS45FlatCommonChartReal d n => Fminus0 x * phi x
  have hEdge_eq : AdjEdge = OrdEdge := by
    -- This is the exact side-height transfer body below:
    -- choose `eta0`, `Keta := {eta0}`; define `psi0`, `psiPlus`,
    -- `psiMinus`, `BranchPlusSide`, `BranchMinusSide`, `SourcePlusSide`, and
    -- `SourceMinusSide`; prove `hBranchPlus_zero` and `hBranchMinus_zero` by
    -- `SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing`; prove the
    -- checked source common limits by
    -- `D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`;
    -- prove `hPlus_asymptotic_eta0` and `hMinus_asymptotic_eta0` from the
    -- ordinary `(4.1)` and retained raw `(4.12)` branch/source transfer
    -- bodies; turn them into singleton-uniform limits; then apply
    -- `SCV.eq_zeroHeight_of_common_sideLimit`.
  simpa [AdjEdge, OrdEdge] using hEdge_eq

have hzero_plus :
    forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
      HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
      tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fplus0 x * phi x) =
        Tlocal phi := by
  intro phi hphi_compact hphiE
  -- `Tlocal` is the checked ordinary flat edge CLM, so the plus zero-height
  -- pairing is just its pointwise formula on the chosen flat test.
  simpa [Tlocal, Fplus0] using
    (BHW.os45FlatCommonChart_ordinaryEdgeCLM_apply hd OS lgc P phi).symm

have hzero_minus :
    forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
      HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
      tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fminus0 x * phi x) =
        Tlocal phi := by
  intro phi hphi_compact hphiE
  exact (h414_integrals phi hphi_compact hphiE).trans
    (hzero_plus phi hphi_compact hphiE)

obtain ⟨Wflat, hWflat_open, hWflat_pre, hzedgeWflat,
    hWflat_sub, hWflat_eq⟩ :=
  BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
    (d := d) hd OS lgc (P := P)
    hE_open hE_sub ys hys_mem hys_li x0 hx0
    Tlocal hzero_plus hzero_minus
```

The bridge returns an ambient complex-open seed:

```lean
exists W : Set (Fin n -> Fin (d + 1) -> Complex),
  IsOpen W /\
  IsPreconnected W /\
  zedge in W /\
  W <= BHW.ExtendedTube d n inter
       BHW.permutedExtendedTubeSector d n P.τ /\
  Set.EqOn
    (BHW.extendF (bvt_F OS lgc n))
    (fun z =>
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.τ z))
    W
```

Inside Stage A this seed is used only as the local comparison seed for the
flat crossing.  It is not a common-boundary CLM and it is not a local SPrime
branch.

### Retired Source Representation Leaf

The old transcript below spelled the flat crossing as a full
`hsource_zero_rep` proof body.  That route is now retired for the upstream
flat crossing: the Lean file consumes the local zero-height pairings directly
through `flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM`.  Keep
this block only as an audit of why the source-representation wrapper was
removed; do not implement it as the active hgrid input.

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
  intro psi hpsiU
  rcases hpsiU with ⟨hpsi_compact, hpsi_suppU⟩
  have hlocal :
      forall u in tsupport (psi : NPointDomain d n -> Complex),
        exists V : Set (NPointDomain d n),
          IsOpen V /\
          u in V /\
          ContinuousOn Ghoriz V /\
          SCV.RepresentsDistributionOn
            (0 : SchwartzMap (NPointDomain d n) Complex ->L[Complex] Complex)
            Ghoriz V := by
    intro u hu
    have huU : u in Ulocal := hpsi_suppU hu
    -- Choose a small connected precompact source window `V` around `u`
    -- with `closure V <= Ulocal` and hence `closure V <= P.V`.
    obtain ⟨V, hV_open, hV_connected, huV, hV_compact,
        hV_closure_Ulocal⟩ :=
      BHW.exists_connected_open_precompact_subset hUlocal_open huU
    have hV_closure_P : closure V <= P.V :=
      hV_closure_Ulocal.trans hUlocal_sub

    have hV_cont : ContinuousOn Ghoriz V := by
      exact
        BHW.continuousOn_os45CommonEdge_pulledRealBranchDifference_trace
          (d := d) hd OS lgc (P := P)
          (show V <= P.V from subset_closure.trans hV_closure_P)

    have hV_rep :
        SCV.RepresentsDistributionOn
          (0 : SchwartzMap (NPointDomain d n) Complex ->L[Complex] Complex)
          Ghoriz V := by
      intro chi hchiV
      rcases hchiV with ⟨hchi_compact, hchi_suppV⟩
      -- Local OS-I `(4.14)` transfer for this source window:
      --   ordinary incoming sheet:
      --     `BHW.ExtendedTube d n ∩ H.ΩJ`, branch `extendF (bvt_F OS lgc n)`;
      --   raw-adjacent incoming sheet:
      --     `{z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ`,
      --     branch `fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)`;
      --   outgoing side sheets:
      --     `BHW.os45FlatCommonChartOmega d n 1` and
      --     `BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)`;
      --   endpoint traces:
      --     ordinary trace at `t = 0`, adjacent raw trace transported to the
      --     endpoint chart and rewritten to `extendF o permAct` only there.
      -- The proof below keeps all objects local to `V`: it builds the flat
      -- test `phiChi`, proves the flat zero by side-height branch/source
      -- asymptotics, pulls the zero back to the source chart, and cancels the
      -- nonzero flat Jacobian.
      have hhorizontal_zero :
          integral (fun u : NPointDomain d n => Ghoriz u * chi u) = 0 := by
        classical
        let e :=
          BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
        let Jflat : Complex :=
          (BHW.os45CommonEdgeFlatJacobianAbs n : Complex)
        let phiChi :
            SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex :=
          (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm) chi

        have hV_sub_P : V <= P.V :=
          subset_closure.trans hV_closure_P
        have hV_sub_Ulocal : V <= Ulocal :=
          subset_closure.trans hV_closure_Ulocal
        have hphiChi_compact :
            HasCompactSupport
              (phiChi : BHW.OS45FlatCommonChartReal d n -> Complex) := by
          -- Compact support is carried by the homeomorphism `e.symm`.
          simpa [phiChi, e, Function.comp_def,
            SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
            hchi_compact.comp_homeomorph e.symm.toHomeomorph
        have hphiChi_image :
            tsupport
                (phiChi : BHW.OS45FlatCommonChartReal d n -> Complex) <=
              e '' V := by
          intro x hx
          have hxpre :
              e.symm x in tsupport (chi : NPointDomain d n -> Complex) := by
            have hpre :=
              tsupport_comp_subset_preimage
                (chi : NPointDomain d n -> Complex) e.symm.continuous
            simpa [phiChi, e, Function.comp_def,
              SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hpre hx
          exact ⟨e.symm x, hchi_suppV hxpre, by simp [e]⟩
        have hphiChiUlocal :
            tsupport
                (phiChi : BHW.OS45FlatCommonChartReal d n -> Complex) <=
              e '' Ulocal :=
          hphiChi_image.trans (Set.image_mono hV_sub_Ulocal)
        have hphiChiE :
            tsupport
                (phiChi : BHW.OS45FlatCommonChartReal d n -> Complex) <=
              BHW.os45FlatCommonChartEdgeSet d n P
                (1 : Equiv.Perm (Fin n)) := by
          intro x hx
          rcases hphiChi_image hx with ⟨u, huV, rfl⟩
          exact
            (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
              (1 : Equiv.Perm (Fin n)) u).mpr (hV_sub_P huV)
        have hpull_chi :
            forall u : NPointDomain d n,
              (D.toSchwartzNPointCLM
                  (1 : Equiv.Perm (Fin n)) phiChi :
                NPointDomain d n -> Complex) u = chi u := by
          intro u
          calc
            (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) phiChi :
              NPointDomain d n -> Complex) u
                = phiChi (e u) := by
                    exact
                      D.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
                        (1 : Equiv.Perm (Fin n)) phiChi hphiChiE u
            _ = chi u := by
                    simp [phiChi, e,
                      SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

        let FlatDiff :
            BHW.OS45FlatCommonChartReal d n -> Complex := fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (fun a => (x a : Complex)) -
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex))

        have hflat_zero_phiChi :
            integral
              (fun x : BHW.OS45FlatCommonChartReal d n =>
                FlatDiff x * phiChi x) = 0 := by
          -- Instantiate the exact side-height `(4.14)` transfer leaf below with
          -- `phi := phiChi`, `hphi_compact := hphiChi_compact`, and
          -- `hphiE := hphiChiE`, `hphiUlocal := hphiChiUlocal`.  This is
          -- deliberately in-body: the following names are local `have`s, not
          -- exported wrapper theorem surfaces.
          let l := nhdsWithin (0 : Real) (Set.Ioi 0)
          obtain ⟨hCone_open, hCone_conv, hCone_zero, hCone_scale,
              hCone_nonempty⟩ :=
            BHW.os45FlatCommonChartCone_eowReady d n
          obtain ⟨eta0, heta0⟩ := hCone_nonempty
          let Keta : Set (BHW.OS45FlatCommonChartReal d n) := {eta0}
          have hKeta : IsCompact Keta := by
            simp [Keta]
          have hKetaC :
              Keta <= BHW.os45FlatCommonChartCone d n := by
            intro eta heta
            simpa [Keta] using heta0
          let psi0 : ZeroDiagonalSchwartz d n :=
            D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phiChi
          let psiPlus : Real -> BHW.OS45FlatCommonChartReal d n ->
              ZeroDiagonalSchwartz d n := fun eps eta =>
            D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta phiChi
          let psiMinus : Real -> BHW.OS45FlatCommonChartReal d n ->
              ZeroDiagonalSchwartz d n := fun eps eta =>
            D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta phiChi
          let BranchPlusSide :
              Real -> BHW.OS45FlatCommonChartReal d n -> Complex :=
            fun eps eta =>
              integral fun x : BHW.OS45FlatCommonChartReal d n =>
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (fun a => (x a : Complex) +
                    (eps : Complex) * (eta a : Complex) * Complex.I) *
                  phiChi x
          let BranchMinusSide :
              Real -> BHW.OS45FlatCommonChartReal d n -> Complex :=
            fun eps eta =>
              integral fun x : BHW.OS45FlatCommonChartReal d n =>
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (fun a => (x a : Complex) -
                    (eps : Complex) * (eta a : Complex) * Complex.I) *
                  phiChi x
          let SourcePlusSide :
              Real -> BHW.OS45FlatCommonChartReal d n -> Complex :=
            fun eps eta =>
              Jflat *
                integral fun u : NPointDomain d n =>
                  bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
                    ((((psiPlus eps eta).1 : SchwartzNPoint d n) :
                      NPointDomain d n -> Complex) u)
          let SourceMinusSide :
              Real -> BHW.OS45FlatCommonChartReal d n -> Complex :=
            fun eps eta =>
              Jflat *
                integral fun u : NPointDomain d n =>
                  bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
                    ((((psiMinus eps eta).1 : SchwartzNPoint d n) :
                      NPointDomain d n -> Complex) u)
          let Usource : Set (NPointDomain d n) := V
          let Ksource : Set (NPointDomain d n) := closure V
          have hUsource_open : IsOpen Usource := by
            simpa [Usource] using hV_open
          have hUsource_sub_Ksource : Usource <= Ksource := by
            intro u hu
            exact subset_closure hu
          have hKsource_compact : IsCompact Ksource := by
            simpa [Ksource] using hV_compact
          have hKsource_sub_P : Ksource <= P.V := by
            simpa [Ksource] using hV_closure_P
          have hphiUsource :
              tsupport
                  (phiChi : BHW.OS45FlatCommonChartReal d n -> Complex) <=
                e '' Usource := by
            simpa [Usource] using hphiChi_image
          let OrdEdge : Complex :=
            integral fun x : BHW.OS45FlatCommonChartReal d n =>
              BHW.os45FlatCommonChartBranch d n OS lgc
                (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex)) *
                phiChi x
          let AdjEdge : Complex :=
            integral fun x : BHW.OS45FlatCommonChartReal d n =>
              BHW.os45FlatCommonChartBranch d n OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (fun a => (x a : Complex)) * phiChi x

          have hΩplus_open :
              IsOpen
                (BHW.os45FlatCommonChartOmega d n
                  (1 : Equiv.Perm (Fin n))) :=
            BHW.isOpen_os45FlatCommonChartOmega d n
              (1 : Equiv.Perm (Fin n))
          have hΩminus_open :
              IsOpen
                (BHW.os45FlatCommonChartOmega d n
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
            BHW.isOpen_os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          have hFplus_cont :
              ContinuousOn
                (BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n)))
                (BHW.os45FlatCommonChartOmega d n
                  (1 : Equiv.Perm (Fin n))) :=
            (BHW.differentiableOn_os45FlatCommonChartBranch
              d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn
          have hFminus_cont :
              ContinuousOn
                (BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n))))
                (BHW.os45FlatCommonChartOmega d n
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
            (BHW.differentiableOn_os45FlatCommonChartBranch
              d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn
          have hplus_real_mem :
              forall x in BHW.os45FlatCommonChartEdgeSet d n P
                  (1 : Equiv.Perm (Fin n)),
                (fun a => (x a : Complex)) in
                  BHW.os45FlatCommonChartOmega d n
                    (1 : Equiv.Perm (Fin n)) :=
            BHW.os45FlatCommonChart_real_mem_omega_id (d := d) hd (P := P)
          have hminus_real_mem :
              forall x in BHW.os45FlatCommonChartEdgeSet d n P
                  (1 : Equiv.Perm (Fin n)),
                (fun a => (x a : Complex)) in
                  BHW.os45FlatCommonChartOmega d n
                    (P.τ.symm * (1 : Equiv.Perm (Fin n))) :=
            BHW.os45FlatCommonChart_real_mem_omega_adjacent
              (d := d) hd (P := P)
          have hplus_side :
              forall K, IsCompact K ->
                K <= BHW.os45FlatCommonChartEdgeSet d n P
                  (1 : Equiv.Perm (Fin n)) ->
                forall Kη, IsCompact Kη ->
                  Kη <= BHW.os45FlatCommonChartCone d n ->
                  exists r : Real, 0 < r /\
                    forall x in K, forall eta in Kη,
                      forall eps : Real, 0 < eps -> eps < r ->
                        (fun a => (x a : Complex) +
                          ((1 : Real) : Complex) * (eps : Complex) *
                            (eta a : Complex) * Complex.I) in
                          BHW.os45FlatCommonChartOmega d n
                            (1 : Equiv.Perm (Fin n)) := by
            intro K hK hKE Kη hKη hKηC
            obtain <r, hr, hside> :=
              BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
                (d := d) hd (P := P) K hK hKE Kη hKη hKηC
            refine <r, hr, ?_>
            intro x hx eta heta eps heps hlt
            simpa [one_mul] using (hside x hx eta heta eps heps hlt).1
          have hminus_side :
              forall K, IsCompact K ->
                K <= BHW.os45FlatCommonChartEdgeSet d n P
                  (1 : Equiv.Perm (Fin n)) ->
                forall Kη, IsCompact Kη ->
                  Kη <= BHW.os45FlatCommonChartCone d n ->
                  exists r : Real, 0 < r /\
                    forall x in K, forall eta in Kη,
                      forall eps : Real, 0 < eps -> eps < r ->
                        (fun a => (x a : Complex) +
                          ((-1 : Real) : Complex) * (eps : Complex) *
                            (eta a : Complex) * Complex.I) in
                          BHW.os45FlatCommonChartOmega d n
                            (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
            intro K hK hKE Kη hKη hKηC
            obtain <r, hr, hside> :=
              BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
                (d := d) hd (P := P) K hK hKE Kη hKη hKηC
            refine <r, hr, ?_>
            intro x hx eta heta eps heps hlt
            simpa [sub_eq_add_neg, neg_mul, one_mul] using
              (hside x hx eta heta eps heps hlt).2

          have hKeta_nonempty : Keta.Nonempty := by
            exact ⟨eta0, by simp [Keta]⟩
          have hBranchPlus_zero :
              TendstoUniformlyOn BranchPlusSide
                (fun _ : BHW.OS45FlatCommonChartReal d n => OrdEdge)
                l Keta := by
            -- Zero-height continuity of the ordinary flat branch at the edge.
            -- Use `SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing`
            -- with literal target `OrdEdge` and `hzero := by rfl`.  Do not
            -- call the CLM zero-height reducer here, since it would require
            -- the equality being proved in this block.
            exact
              SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
                hΩplus_open
                (BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n)))
                hFplus_cont hplus_real_mem
                (1 : Real) hplus_side
                Keta hKeta hKetaC
                phiChi hphiChi_compact hphiChiE
                OrdEdge (by rfl)
          have hBranchMinus_zero :
              TendstoUniformlyOn BranchMinusSide
                (fun _ : BHW.OS45FlatCommonChartReal d n => AdjEdge)
                l Keta := by
            -- Same neutral side-continuity theorem on the retained raw
            -- adjacent flat branch, with literal target `AdjEdge`.
            exact
              SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
                hΩminus_open
                (BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n))))
                hFminus_cont hminus_real_mem
                (-1 : Real) hminus_side
                Keta hKeta hKetaC
                phiChi hphiChi_compact hphiChiE
                AdjEdge (by rfl)
          have hSourcePlus_common :
              TendstoUniformlyOn SourcePlusSide
                (fun _ : BHW.OS45FlatCommonChartReal d n =>
                  Jflat * OS.S n psi0) l Keta := by
            -- Checked signed source-test Schwinger limit for
            -- `D.toSideZeroDiagonalCLM 1 (+1) eps eta phiChi`.
            have hsrc :=
              D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
                OS lgc Keta hKeta hKetaC
                phiChi hphiChi_compact hphiChiE
            exact hsrc.1.const_mul Jflat
          have hSourceMinus_common :
              TendstoUniformlyOn SourceMinusSide
                (fun _ : BHW.OS45FlatCommonChartReal d n =>
                  Jflat * OS.S n psi0) l Keta := by
            -- Checked signed source-test Schwinger limit for
            -- `D.toSideZeroDiagonalCLM 1 (-1) eps eta phiChi`.
            have hsrc :=
              D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
                OS lgc Keta hKeta hKetaC
                phiChi hphiChi_compact hphiChiE
            exact hsrc.2.2.2.const_mul Jflat
          have hOrd_endpoint_mem_on_Ksource :
              forall u in Ksource,
                sourceSide (1 : Real) 0 eta0 u in
                  chainOrd.terminalCarrier := by
            intro u huK
            have huP : u in P.V := hKsource_sub_P huK
            rw [BHW.os45FlatCommonChartSourceSide_zero]
            exact chainOrd.terminal_contains_ordinaryCommonEdge u huP
          have hAdj_endpoint_mem_on_Ksource :
              forall u in Ksource,
                sourceSide (-1 : Real) 0 eta0 u in
                  chainAdj.terminalCarrier := by
            intro u huK
            have huP : u in P.V := hKsource_sub_P huK
            rw [BHW.os45FlatCommonChartSourceSide_zero]
            exact chainAdj.terminal_contains_adjacentCommonEdge u huP

          have hPlus_asymptotic_eta0 :
              Tendsto
                (fun eps =>
                  BranchPlusSide eps eta0 - SourcePlusSide eps eta0)
                l (nhds (0 : Complex)) := by
            -- Paste the ordinary transfer body here, with `phi := phiChi`:
            -- `hplus_sheet` from the checked side-sheet packet;
            -- `hplus_pullback` from the signed branch/source pullback;
            -- `hpsiPlus_move` from side-test convergence;
            -- `hBranchPlus_to_common` by the local subchain
            --   `Word := chainOrd.terminalBoundaryCLM`,
            --   `hOrd_integrand_to_endpoint`,
            --   `hOrd_integral_rewrite`,
            --   `hOrd_fixed_psi0` from the ordinary `(4.1)` fixed leaf and
            --     checked scalar cancellation for the concrete compact
            --     `psi0`,
            --   `hOrd_moving` from the checked common-compact-support
            --     perturbation theorem,
            --   `hOrd_boundary_to_source` by endpoint DCT and
            --     `tendsto_nhds_unique`,
            --   `hOrd_source_norm` by the ordinary Wick/source
            --     normalization, and
            --   `hOrd_as_extendF.const_mul Jflat`;
            -- `hSourcePlus_eta0 := hSourcePlus_common.tendsto hKeta_eta0`;
            -- `hbranch := hBranchPlus_to_common.congr' hplus_pullback.symm`;
            -- finish by
            -- `hbranch.sub hSourcePlus_eta0` and the filter-level ring
            -- rewrite.  All names remain local to `hhorizontal_zero`.
          have hMinus_asymptotic_eta0 :
              Tendsto
                (fun eps =>
                  BranchMinusSide eps eta0 - SourceMinusSide eps eta0)
                l (nhds (0 : Complex)) := by
            -- Paste the raw-adjacent transfer body here, with `phi := phiChi`:
            -- `hminus_sheet` from the checked side-sheet packet;
            -- `hminus_pullback` from the signed pullback with
            --   `σ = P.τ.symm * 1`, followed by terminal endpoint equality
            --   supplied by the retained raw `(4.12)` chain;
            -- `hpsiMinus_move` from side-test convergence;
            -- `hBranchMinus_to_common` by the local subchain
            --   `Wadj := chainAdj.terminalBoundaryCLM`,
            --   `hAdj_integrand_to_endpoint`,
            --   `hAdj_integral_rewrite`,
            --   `hAdj_fixed_psi0` from the raw `(4.12)` fixed leaf and
            --     checked scalar cancellation for the concrete compact
            --     `psi0`,
            --   `hAdj_moving` from the checked common-compact-support
            --     perturbation theorem,
            --   `hAdj_boundary_to_source` by endpoint DCT and
            --     `tendsto_nhds_unique`,
            --   `hAdj_source_norm` by the adjacent Wick/source normalizer,
            --     after endpoint transport, and
            --   `hAdj_as_terminal.const_mul Jflat`;
            -- `hSourceMinus_eta0 := hSourceMinus_common.tendsto hKeta_eta0`;
            -- `hbranch := hBranchMinus_to_common.congr' hminus_pullback.symm`;
            -- finish by
            -- `hbranch.sub hSourceMinus_eta0` and the filter-level ring
            -- rewrite.  The deterministic adjacent endpoint formula appears
            -- only after the raw chain has supplied terminal equality.
          have hPlus_asymptotic :
              TendstoUniformlyOn
                (fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
                (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
                l Keta := by
            simpa [Keta] using
              (SCV.tendstoUniformlyOn_singleton_iff_tendsto
                (F := fun eps eta =>
                  BranchPlusSide eps eta - SourcePlusSide eps eta)
                (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
                (p := l) (x := eta0)).2 hPlus_asymptotic_eta0
          have hMinus_asymptotic :
              TendstoUniformlyOn
                (fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
                (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
                l Keta := by
            simpa [Keta] using
              (SCV.tendstoUniformlyOn_singleton_iff_tendsto
                (F := fun eps eta =>
                  BranchMinusSide eps eta - SourceMinusSide eps eta)
                (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
                (p := l) (x := eta0)).2 hMinus_asymptotic_eta0
          have hBranchPlus_common :
              TendstoUniformlyOn BranchPlusSide
                (fun _ : BHW.OS45FlatCommonChartReal d n =>
                  Jflat * OS.S n psi0) l Keta :=
            SCV.tendstoUniformlyOn_of_sub_tendstoUniformlyOn_zero
              hPlus_asymptotic hSourcePlus_common
          have hBranchMinus_common :
              TendstoUniformlyOn BranchMinusSide
                (fun _ : BHW.OS45FlatCommonChartReal d n =>
                  Jflat * OS.S n psi0) l Keta :=
            SCV.tendstoUniformlyOn_of_sub_tendstoUniformlyOn_zero
              hMinus_asymptotic hSourceMinus_common
          have hEdge_eq : AdjEdge = OrdEdge :=
            SCV.eq_zeroHeight_of_common_sideLimit
              hKeta_nonempty
              hBranchMinus_zero hBranchPlus_zero
              hBranchMinus_common hBranchPlus_common
          -- Expand `FlatDiff`, `AdjEdge`, and `OrdEdge`; discharge the last
          -- line by compact-support integrability, `integral_sub`, and
          -- `sub_eq_zero.mpr hEdge_eq`.
          simpa [FlatDiff, AdjEdge, OrdEdge, sub_mul] using
            sub_eq_zero.mpr hEdge_eq

        have hcov :=
          BHW.os45FlatCommonChart_commonBoundaryDifference_integral_eq_sourcePullback
            (d := d) hd OS lgc (P := P) D
            phiChi hphiChi_compact hphiChiE
        have hJ_ne : Jflat ≠ 0 := by
          exact_mod_cast
            (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
        have hJmul_zero :
            Jflat *
              integral
                (fun u : NPointDomain d n =>
                  Ghoriz u *
                    (D.toSchwartzNPointCLM
                      (1 : Equiv.Perm (Fin n)) phiChi :
                      NPointDomain d n -> Complex) u) = 0 := by
          rw [← hcov]
          simpa [FlatDiff, Ghoriz, Jflat] using hflat_zero_phiChi
        have hsource_pulled_zero :
            integral
              (fun u : NPointDomain d n =>
                Ghoriz u *
                  (D.toSchwartzNPointCLM
                    (1 : Equiv.Perm (Fin n)) phiChi :
                    NPointDomain d n -> Complex) u) = 0 :=
          (mul_eq_zero.mp hJmul_zero).resolve_left hJ_ne
        have hsource_pullback_integral :
            integral
              (fun u : NPointDomain d n =>
                Ghoriz u *
                  (D.toSchwartzNPointCLM
                    (1 : Equiv.Perm (Fin n)) phiChi :
                    NPointDomain d n -> Complex) u) =
            integral (fun u : NPointDomain d n => Ghoriz u * chi u) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun u => by
            rw [hpull_chi u]
        exact hsource_pullback_integral ▸ hsource_pulled_zero

      simpa using hhorizontal_zero.symm

    exact ⟨V, hV_open, huV, hV_cont, hV_rep⟩

  have hrep :=
    SCV.distribution_representation_of_local_representations_for_test
      (T := (0 : SchwartzMap (NPointDomain d n) Complex ->L[Complex] Complex))
      (H := Ghoriz) (phi := psi) hpsi_compact hlocal
  simpa [Ghoriz] using hrep
```

The line `hhorizontal_zero` is now expanded down to the real compact-test
boundary-transfer theorem.  A previous draft called this transfer
`BHW.os45CommonEdge_horizontalPairing_eq_wickPairing_of_OSI45` and made it
return a compactly supported Wick-side test `chiWick`.  That is not an active
Lean primitive, and the latest theorem-shape audit rejects it:
analytic continuation of boundary distributions supplies side-height limits,
not a literal compact-support transform from a zero-height horizontal test to
a finite Wick-height test.  It must not be implemented or used.

The active proof target is instead the boundary-limit form below.  The paper
anchor is the locality paragraph: Euclidean symmetry together with `(4.1)`,
raw transported `(4.12)`, and `(4.14)` gives the symmetric analytic
continuation on the permuted tube family before the
Bargmann-Hall-Wightman enlargement and before Jost's boundary-locality theorem.
Here `(4.14)` is the Lorentz-covariance equation for the Fourier-Laplace
distributions; it is used to compare branch-side side-height pairings with the
source-side Fourier-Laplace pairings.  It is not by itself a flat real-edge
equality.  The local proof obligations are:

1. Ordinary endpoint: use the ordinary one-branch chain to identify the
   terminal ordinary branch with `BHW.extendF (bvt_F OS lgc n)` on
   `BHW.ExtendedTube d n ∩ H.ΩJ`, and use
   `BHW.os45Figure24Path_endpoint_extendF_eq_ordinaryPulledRealBranch` for
   the horizontal trace.
2. Adjacent endpoint: use the retained raw `(4.12)` chain, starting from
   `OmegaSeed412/BSeed412` at `zadj`, to identify the terminal adjacent branch.
   The endpoint may be rewritten by
   `BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch`
   only after that chain has transported the raw `(4.12)` germ to the
   endpoint-centered chart.
3. Source-side common limit: use the checked
   `BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`
   only for the signed source-test families.  This is a limit statement; it is
   not a finite-height equality and it is not an individual zero-height
   flat-edge normalization.
4. Branch-side to source-side transfer: prove the two genuine OS-I `(4.14)`
   asymptotic trace-transfer local `have`s `hPlus_asymptotic` and
   `hMinus_asymptotic`.  These are the hard proof bodies to implement.  They compare
   the ordinary plus-side flat branch integral and the transported adjacent
   minus-side flat branch integral with their corresponding source
   Fourier-Laplace pairings as `eps -> 0+`, uniformly on the chosen compact
   cone-direction singleton.  The adjacent theorem must carry the raw
   `OmegaSeed412/BSeed412` chain provenance; it may not replace it by
   `extendF ∘ permAct`.
5. Zero-height conclusion: combine the checked zero-height side-continuity
   theorem `SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing`, the two
   checked source common limits, the two `(4.14)` asymptotic transfers, and the
   checked filter lemma `SCV.eq_zeroHeight_of_common_sideLimit` to get
   `AdjEdge = OrdEdge`.  Then use the checked source/flat change-of-variables
   lemmas to rewrite this as `integral (fun u => Ghoriz u * chi u) = 0`.

The two transfers in item 4 should be proved by the following concrete
side-height calculation, now expanded down to the local fixed-test,
endpoint-DCT, and source-normalization sub-haves.

For the plus/ordinary side, first perform the real source-to-flat change of
variables with the translated real variable, not with the zero-height
variable.  For small positive `eps`, support and cutoff removal are now checked
by

```lean
BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_tsupport_subset_image_eventually
BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_eventually
BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually
```

Thus, after shrinking the positive side-height filter, the moving source test
has the pointwise form

```lean
(((psiPlus eps eta0).1 : SchwartzNPoint d n) :
    NPointDomain d n -> Complex) u
  =
    phi (BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) u
      + eps • eta0)
```

Hence the branch-side integral is not compared to a finite Wick test.  It is
first rewritten as the same moving real test paired with the ordinary
side-height boundary branch:

```lean
let OrdSideBranch : Real -> NPointDomain d n -> Complex := fun eps u =>
  BHW.os45FlatCommonChartBranch d n OS lgc
    (1 : Equiv.Perm (Fin n))
    (fun a =>
      ((BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) u a
          + eps * eta0 a : Real) : Complex) +
        (eps : Complex) * (eta0 a : Complex) * Complex.I)

have hBranchPlus_pullback :
    ∀ᶠ eps in l,
      BranchPlusSide eps eta0 =
        Jflat *
          integral fun u : NPointDomain d n =>
            OrdSideBranch eps u *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
  have hSideEdgeSupport :
      ∀ᶠ eps in l, ∀ eta ∈ Keta,
        tsupport (SCV.translateSchwartz (eps • eta) phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) ∧
        tsupport (SCV.translateSchwartz ((-eps : Real) • eta) phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) := by
    obtain <rEdge, hrEdge_pos, hEdge> :=
      BHW.os45FlatCommonChart_sideSupport_radius
        (d := d) (P := P) Keta hKeta hKetaC
        phi hphi_compact hphiE
    filter_upwards
      [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hrEdge_pos)]
      with eps heps_pos heps_lt eta heta
    exact hEdge eps heps_pos heps_lt eta heta
  filter_upwards [hSideEdgeSupport] with eps heps_support
  have hphiE_plus :
      tsupport (SCV.translateSchwartz (((1 : Real) * eps) • eta0) phi :
        BHW.OS45FlatCommonChartReal d n -> Complex) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P (1 : Equiv.Perm (Fin n)) :=
    by simpa [one_mul] using (heps_support eta0 hKeta_eta0).1
  exact
    BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM
      (d := d) (n := n) OS lgc D
      (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
      (1 : Real) eps eta0 phi hphiE_plus
      hBranchPlus_integrable_shifted
```

Here `hSideEdgeSupport` is the eventual positive-height flat-edge packet
supplied by `BHW.os45FlatCommonChart_sideSupport_radius`, while source-window
support and pointwise cutoff removal come separately from
`D.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually`, and
`hBranchPlus_integrable_shifted` is discharged by the checked
`BHW.os45FlatCommonChart_branch_shifted_mul_integrable` from compact support
and the ordinary side-domain membership supplied by the local wedge theorem;
the uniform compact-direction eventual package is checked as
`BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually`.
The checked theorem used above expands to the translated CLE Jacobian theorem
plus cutoff removal; it contains no Wick or Schwinger normalization.

The OS-I `(4.1)/(4.14)` leaf is then exactly the boundary-value statement
for this moving source test:

```lean
have hBranchPlus_to_sourceCommon :
    Tendsto
      (fun eps =>
        Jflat *
          integral fun u : NPointDomain d n =>
            OrdSideBranch eps u *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
      l
      (nhds
        (Jflat *
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))) := by
  -- Use the ordinary `(4.1)` endpoint chain to identify the terminal branch
  -- with the OS-I Fourier-Laplace analytic element on the ordinary sheet.
  -- Use `(4.14)` Lorentz covariance of the Fourier-Laplace distribution to
  -- identify its side-height boundary functional on the Figure-2-4 flat
  -- side with the source Wick-section functional.
      -- The moving-test part is the checked Banach-Steinhaus layer after the
      -- ordinary local boundary CLM has been identified: use
      -- `tube_boundaryValueData_moving_of_fixed` / `bvt_boundary_values_moving` only
      -- in literal tube coordinates, and use the compact-support perturbation
      -- estimate in the OS45 common flat chart.  The final equality with `OS.S` is
      -- the checked source
      -- restriction theorem for zero-diagonal tests, applied to
      -- `D.toZeroDiagonalCLM 1 phi`.
      -- This local limit is implemented by the expanded
      -- `hPlus_asymptotic_eta0` body in the exact side-height transfer block
      -- below: `hplus_pullback`, `hOrd_integrand_to_endpoint`,
      -- `hOrd_fixed_psi0`, `hOrd_endpoint_limit`,
      -- `hOrd_boundary_to_source`, `hOrd_source_norm`, and the final
      -- `const_mul Jflat`.  Do not replace that sequence by a public theorem
      -- that assumes this limit.
```

The already checked source-side limit supplies the other half:

```lean
have hSourcePlus_eta0 :
    Tendsto
      (fun eps => SourcePlusSide eps eta0)
      l
      (nhds
        (Jflat *
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))) := by
  exact (hSourcePlus_common.tendsto hKeta_eta0)
```

Then the ordinary transfer is only filter algebra:

```lean
have hPlus_asymptotic_eta0 :
    Tendsto
      (fun eps => BranchPlusSide eps eta0 - SourcePlusSide eps eta0)
      l (nhds (0 : Complex)) := by
  have hbranch :=
    hBranchPlus_to_sourceCommon.congr' hBranchPlus_pullback.symm
  exact hbranch.sub hSourcePlus_eta0 |>.congr' (by filter_upwards with eps; ring)
```

The adjacent/minus side has the same shape, with two strict differences:

* the side branch is

```lean
let AdjSideBranch : Real -> NPointDomain d n -> Complex := fun eps u =>
  BHW.os45FlatCommonChartBranch d n OS lgc
    (P.τ.symm * (1 : Equiv.Perm (Fin n)))
    (fun a =>
      ((BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) u a
          - eps * eta0 a : Real) : Complex) -
        (eps : Complex) * (eta0 a : Complex) * Complex.I)
```

* the boundary-value CLM must come from the transported raw
  `OmegaSeed412/BSeed412` analytic element.  The proof may rewrite the terminal
  endpoint by
  `BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch`
  only after the raw `(4.12)` chain has reached that endpoint-centered chart.
  It may not use `extendF o permAct` as the upstream adjacent seed.

Thus the adjacent proof has the exact same three layers:

```lean
have hBranchMinus_pullback :
    ∀ᶠ eps in l,
      BranchMinusSide eps eta0 =
        Jflat *
          integral fun u : NPointDomain d n =>
            AdjSideBranch eps u *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
  -- Reuse the `hSideEdgeSupport` packet built from
  -- `BHW.os45FlatCommonChart_sideSupport_radius`; do not read edge support
  -- from the source-window cutoff-removal packet.
  filter_upwards [hSideEdgeSupport] with eps heps_support
  have hphiE_minus :
      tsupport (SCV.translateSchwartz (((-1 : Real) * eps) • eta0) phi :
        BHW.OS45FlatCommonChartReal d n -> Complex) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P (1 : Equiv.Perm (Fin n)) :=
    by
      simpa [neg_smul, neg_mul, one_mul] using
        (heps_support eta0 hKeta_eta0).2
  exact
    BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM
      (d := d) (n := n) OS lgc D
      (P.τ.symm * (1 : Equiv.Perm (Fin n))) (1 : Equiv.Perm (Fin n))
      (-1 : Real) eps eta0 phi hphiE_minus
      hBranchMinus_integrable_shifted

have hBranchMinus_to_sourceCommon :
    Tendsto
      (fun eps =>
        Jflat *
          integral fun u : NPointDomain d n =>
            AdjSideBranch eps u *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
      l
      (nhds
        (Jflat *
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))) := by
  -- raw `(4.12)` seed -> one-branch transport -> `(4.14)` boundary CLM
  -- -> source Wick-section normalization.  No deterministic adjacent seed.
  -- This local limit is implemented by the expanded
  -- `hMinus_asymptotic_eta0` body below: `hminus_pullback`,
  -- `hAdj_integrand_to_endpoint`, `hAdj_fixed_psi0`,
  -- `hAdj_endpoint_limit`, `hAdj_boundary_to_source`,
  -- `hAdj_source_norm`, and the final `const_mul Jflat`.  Do not replace that
  -- sequence by a public theorem that assumes this limit.

have hSourceMinus_eta0 :
    Tendsto
      (fun eps => SourceMinusSide eps eta0)
      l
      (nhds
        (Jflat *
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))) := by
  exact (hSourceMinus_common.tendsto hKeta_eta0)

have hMinus_asymptotic_eta0 :
    Tendsto
      (fun eps => BranchMinusSide eps eta0 - SourceMinusSide eps eta0)
      l (nhds (0 : Complex)) := by
  have hbranch :=
    hBranchMinus_to_sourceCommon.congr' hBranchMinus_pullback.symm
  exact hbranch.sub hSourceMinus_eta0 |>.congr' (by filter_upwards with eps; ring)
```

This is a non-wrapper split: the pullback lemmas prove actual coordinate and
support equalities, the boundary-value leaves prove the OS-I
Fourier-Laplace/covariance limit, and the final subtraction is routine
filter algebra.  A Lean theorem that takes `hBranchPlus_to_sourceCommon`,
`hBranchMinus_to_sourceCommon`, either asymptotic transfer, or `AdjEdge =
OrdEdge` as a hypothesis would still be wrapper churn.

Terminology guard after the Deep Research sanity check: the proof does still
need the individual branch-side boundary values before subtraction, namely
`hBranchPlus_to_sourceCommon` and `hBranchMinus_to_sourceCommon`.  These are
the OS-I/OS-II tempered boundary-value leaves for the moving side-height
families.  What remains retired is the different shortcut that tried to prove
static zero-height flat-edge pairings directly equal to the Wick/Schwinger
anchor without the side-height branch/source transfer.

#### Exact Side-Height `(4.14)` Transfer Leaf

The flat real-Jost step should not try to prove the two zero-height edge
pairings separately by normalizing each one to a Wick/Schwinger anchor.  That
is the retired shortcut.  The Lean target is the common side-limit statement:
the ordinary and retained raw-adjacent side-height branch pairings have the
same limiting value, hence their zero-height edge pairings are equal.

Equivalently, the proof first establishes the two individual moving
side-height boundary-value limits (`hBranchPlus_to_sourceCommon` and
`hBranchMinus_to_sourceCommon`) from OS-I `(4.1)/(4.12)/(4.14)` plus the
OS-II temperedness/growth guard, then subtracts the checked source-side limits.
The asymptotic transfer is therefore a consequence of the individual
boundary-value leaves, not a new public assumption.

The only nonmechanical mathematical inputs left in `hhorizontal_zero` are the
two branch/source asymptotic transfers below.  They are proof-local OS-I
`(4.14)` steps and may not be replaced by hypotheses named
`hsource_zero_rep`, a local common-boundary packet, `Hdiff`, `Wadj`, a finite
`chiWick`, either zero-height equality, or individual zero-height-to-Schwinger
normalization statements.

Common local data inside the proof-local horizontal pairing calculation:

```lean
let l := nhdsWithin (0 : Real) (Set.Ioi 0)
let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
let Jflat : Complex := (BHW.os45CommonEdgeFlatJacobianAbs n : Complex)

let psi0 : ZeroDiagonalSchwartz d n :=
  D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi

let psiPlus : Real -> BHW.OS45FlatCommonChartReal d n ->
    ZeroDiagonalSchwartz d n := fun eps eta =>
  D.toSideZeroDiagonalCLM
    (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta phi

let psiMinus : Real -> BHW.OS45FlatCommonChartReal d n ->
    ZeroDiagonalSchwartz d n := fun eps eta =>
  D.toSideZeroDiagonalCLM
    (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta phi

let BranchPlusSide :
    Real -> BHW.OS45FlatCommonChartReal d n -> Complex := fun eps eta =>
  integral fun x : BHW.OS45FlatCommonChartReal d n =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
      (fun a => (x a : Complex) +
        (eps : Complex) * (eta a : Complex) * Complex.I) * phi x

let BranchMinusSide :
    Real -> BHW.OS45FlatCommonChartReal d n -> Complex := fun eps eta =>
  integral fun x : BHW.OS45FlatCommonChartReal d n =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      (fun a => (x a : Complex) -
        (eps : Complex) * (eta a : Complex) * Complex.I) * phi x

let SourcePlusSide :
    Real -> BHW.OS45FlatCommonChartReal d n -> Complex := fun eps eta =>
  Jflat *
    integral fun u : NPointDomain d n =>
      bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
        ((((psiPlus eps eta).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u)

let SourceMinusSide :
    Real -> BHW.OS45FlatCommonChartReal d n -> Complex := fun eps eta =>
  Jflat *
    integral fun u : NPointDomain d n =>
      bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
        ((((psiMinus eps eta).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u)

let OrdEdge : Complex :=
  integral fun x : BHW.OS45FlatCommonChartReal d n =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex)) * phi x

let AdjEdge : Complex :=
  integral fun x : BHW.OS45FlatCommonChartReal d n =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      (fun a => (x a : Complex)) * phi x
```

The zero-height side-continuity inputs are neutral side-integral continuity
facts with literal endpoint scalar targets.  Do not instantiate
`BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM`
or its minus analogue here unless the target equality has already been proved:
those wrappers require the zero-height equality as an input.  In the live
`hzero_plus`/`hzero_minus` block, using them with `Tlocal` would be circular,
and using them with the zero CLM would assert a false `OrdEdge = 0` or
`AdjEdge = 0` premise.  Use
`SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing` directly.

```lean
have hBranchPlus_zero :
    TendstoUniformlyOn
      BranchPlusSide
      (fun _ : BHW.OS45FlatCommonChartReal d n => OrdEdge)
      l Keta := by
  have hΩplus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n (1 : Equiv.Perm (Fin n))
  have hFplus_cont :
      ContinuousOn
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)))
        (BHW.os45FlatCommonChartOmega d n
          (1 : Equiv.Perm (Fin n))) :=
    (BHW.differentiableOn_os45FlatCommonChartBranch
      d n OS lgc (1 : Equiv.Perm (Fin n))).continuousOn
  have hplus_real_mem :
      forall x in BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)),
        (fun a => (x a : Complex)) in
          BHW.os45FlatCommonChartOmega d n
            (1 : Equiv.Perm (Fin n)) := by
    exact BHW.os45FlatCommonChart_real_mem_omega_id (d := d) hd (P := P)
  have hplus_side :
      forall K, IsCompact K ->
        K <= BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) ->
        forall Kη, IsCompact Kη ->
          Kη <= BHW.os45FlatCommonChartCone d n ->
          exists r : Real, 0 < r /\
            forall x in K, forall eta in Kη, forall eps : Real,
              0 < eps -> eps < r ->
                (fun a => (x a : Complex) +
                  ((1 : Real) : Complex) * (eps : Complex) *
                    (eta a : Complex) * Complex.I) in
                  BHW.os45FlatCommonChartOmega d n
                    (1 : Equiv.Perm (Fin n)) := by
    intro K hK hKE Kη hKη hKηC
    obtain <r, hr, hside> :=
      BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
        (d := d) hd (P := P) K hK hKE Kη hKη hKηC
    refine <r, hr, ?_>
    intro x hx eta heta eps heps hlt
    simpa [one_mul] using (hside x hx eta heta eps heps hlt).1
  simpa [BranchPlusSide, OrdEdge, one_mul] using
    SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
      (m := BHW.os45FlatCommonChartDim d n)
      (E := BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
      (C := BHW.os45FlatCommonChartCone d n)
      (Ωc := BHW.os45FlatCommonChartOmega d n
        (1 : Equiv.Perm (Fin n)))
      hΩplus_open
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)))
      hFplus_cont hplus_real_mem
      (1 : Real) hplus_side
      Keta hKeta hKetaC phi hphi_compact hphiE
      OrdEdge (by rfl)

have hBranchMinus_zero :
    TendstoUniformlyOn
      BranchMinusSide
      (fun _ : BHW.OS45FlatCommonChartReal d n => AdjEdge)
      l Keta := by
  have hΩminus_open :
      IsOpen
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    BHW.isOpen_os45FlatCommonChartOmega d n
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
  have hFminus_cont :
      ContinuousOn
        (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n))))
        (BHW.os45FlatCommonChartOmega d n
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
    (BHW.differentiableOn_os45FlatCommonChartBranch
      d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn
  have hminus_real_mem :
      forall x in BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)),
        (fun a => (x a : Complex)) in
          BHW.os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
    exact BHW.os45FlatCommonChart_real_mem_omega_adjacent
      (d := d) hd (P := P)
  have hminus_side :
      forall K, IsCompact K ->
        K <= BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) ->
        forall Kη, IsCompact Kη ->
          Kη <= BHW.os45FlatCommonChartCone d n ->
          exists r : Real, 0 < r /\
            forall x in K, forall eta in Kη, forall eps : Real,
              0 < eps -> eps < r ->
                (fun a => (x a : Complex) +
                  ((-1 : Real) : Complex) * (eps : Complex) *
                    (eta a : Complex) * Complex.I) in
                  BHW.os45FlatCommonChartOmega d n
                    (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
    intro K hK hKE Kη hKη hKηC
    obtain <r, hr, hside> :=
      BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
        (d := d) hd (P := P) K hK hKE Kη hKη hKηC
    refine <r, hr, ?_>
    intro x hx eta heta eps heps hlt
    simpa [sub_eq_add_neg, neg_mul, one_mul] using
      (hside x hx eta heta eps heps hlt).2
  simpa [BranchMinusSide, AdjEdge, sub_eq_add_neg, neg_mul, one_mul] using
    SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
      (m := BHW.os45FlatCommonChartDim d n)
      (E := BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
      (C := BHW.os45FlatCommonChartCone d n)
      (Ωc := BHW.os45FlatCommonChartOmega d n
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      hΩminus_open
      (BHW.os45FlatCommonChartBranch d n OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))))
      hFminus_cont hminus_real_mem
      (-1 : Real) hminus_side
      Keta hKeta hKetaC phi hphi_compact hphiE
      AdjEdge (by rfl)
```

The source-side common Schwinger limits are already checked by
`D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`.  The plus
side uses the first component and the minus/adjacent side uses the fourth
component, with the flat Jacobian multiplied afterward:

```lean
have hsrc :=
  D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
    OS lgc Keta hKeta hKetaC phi hphi_compact hphiE

have hSourcePlus_common :
    TendstoUniformlyOn SourcePlusSide
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        Jflat * OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))
      l Keta := by
  exact hsrc.1.const_mul Jflat

have hSourceMinus_common :
    TendstoUniformlyOn SourceMinusSide
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        Jflat * OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))
      l Keta := by
  exact hsrc.2.2.2.const_mul Jflat
```

The genuine OS-I `(4.14)` content is the pair of asymptotic transfers below.
For the current implementation, specialize the compact direction set to the
singleton actually used by the side-limit helper:

```lean
let Keta : Set (BHW.OS45FlatCommonChartReal d n) := {eta0}
have hKeta_eta0 : eta0 in Keta := by simp [Keta]
```

The moving-test perturbation leaves also bind a source compact packet in the
same local horizontal compact-test proof body.  For the local precompact source
window use
`Usource := V`, `Ksource := closure V`; hence
`hUsource_open`, `hUsource_sub_Ksource`, `hKsource_compact`, and
`hKsource_sub_P` come from the precompact-window choice
`BHW.exists_connected_open_precompact_subset`.  The support input for the
checked Figure-2-4 moving-test theorem is the original flat test support

```lean
have hphiUsource :
    tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <=
      (BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))) '' Usource
```

not the auxiliary flat pullback test `psi0Flat` used inside the
fixed-test scalar-cancellation subleaf.  The endpoint membership inputs for
the perturbation estimate are then:

```lean
have hOrd_endpoint_mem_on_Ksource :
    forall u in Ksource,
      sourceSide (1 : Real) 0 eta0 u in chainOrd.terminalCarrier := by
  intro u huK
  have huP : u in P.V := hKsource_sub_P huK
  rw [BHW.os45FlatCommonChartSourceSide_zero]
  exact chainOrd.terminal_contains_ordinaryCommonEdge u huP

have hAdj_endpoint_mem_on_Ksource :
    forall u in Ksource,
      sourceSide (-1 : Real) 0 eta0 u in chainAdj.terminalCarrier := by
  intro u huK
  have huP : u in P.V := hKsource_sub_P huK
  rw [BHW.os45FlatCommonChartSourceSide_zero]
  exact chainAdj.terminal_contains_adjacentCommonEdge u huP
```

The later moving-test step is now checked as the SourceSideMoving theorem
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport`.
For each sufficiently small side height, the concrete common-compact-support
and zeroth-seminorm facts feed that theorem, which internally uses the checked
fixed endpoint DCT, the compact-support perturbation estimate, and the
`MeasureTheory.integral_add` split.  This theorem is still only neutral
analytic support: it assumes the selected fixed endpoint limit and does not
select `Word`/`Wadj` or assert a branch/source transfer.

The fixed-test scalar-cancellation step is now checked separately as
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest`.
It is used only after the proof-local flat limit has already been selected from
the ordinary or raw-adjacent one-branch flat boundary trace.  It then applies
the translated-test pullback, cancels the positive Jacobian, and yields the
source-side fixed limit landing in `Word psi0` or `Wadj psi0`.  It is not a
replacement for the flat OS-I `(4.14)` trace selection.

Do not try to prove a new compact-direction boundary-value theorem at this
stage.  The uniform-on-`Keta` statements are obtained from fixed-direction
`Tendsto` statements by `SCV.tendstoUniformlyOn_singleton_iff_tendsto`.

```lean
have hPlus_asymptotic_eta0 :
    Tendsto
      (fun eps => BranchPlusSide eps eta0 - SourcePlusSide eps eta0)
      l (nhds (0 : Complex)) := by
  have hplus_sheet :
      ∀ᶠ eps in l,
        ∀ u : NPointDomain d n,
          e u + eps • eta0 ∈
            tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
          BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
            (sourceSide (1 : Real) eps eta0 u) ∈
            BHW.ExtendedTube d n := by
    -- Use the checked support-local sheet packet and specialize `Keta` to
    -- `{eta0}`.  This is domain bookkeeping for the ordinary outgoing sheet.
    have hsheet :=
      BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually
        (d := d) hd (P := P) Keta hKeta hKetaC
        phi hphi_compact hphiE
    filter_upwards [hsheet] with eps heps u hu
    exact (heps eta0 hKeta_eta0).1 u hu

  have hplus_pullback :
      ∀ᶠ eps in l,
        BranchPlusSide eps eta0 =
          Jflat *
            integral fun u : NPointDomain d n =>
              BHW.extendF (bvt_F OS lgc n)
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
    -- Use the checked branch/source pullback with `σ = 1`, `ρperm = 1`,
    -- `sgn = 1`, plus the eventual support and integrability packets.
    have hinteg :=
      BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
        (d := d) hd OS lgc (P := P) Keta hKeta hKetaC
        phi hphi_compact hphiE
    obtain ⟨rEdge, hrEdge_pos, hEdge⟩ :=
      BHW.os45FlatCommonChart_sideSupport_radius
        (d := d) (P := P) Keta hKeta hKetaC
        phi hphi_compact hphiE
    have hedge_eventually :
        ∀ᶠ eps in l, ∀ eta ∈ Keta,
          tsupport (SCV.translateSchwartz (eps • eta) phi :
            BHW.OS45FlatCommonChartReal d n -> Complex) <=
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) ∧
          tsupport (SCV.translateSchwartz ((-eps : Real) • eta) phi :
            BHW.OS45FlatCommonChartReal d n -> Complex) <=
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) := by
      filter_upwards
        [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds hrEdge_pos)]
        with eps heps_pos heps_lt eta heta
      exact hEdge eps heps_pos heps_lt eta heta
    filter_upwards [hinteg, hedge_eventually]
      with eps hinteg_eps hedge_eps
    exact
      BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
        (d := d) hd OS lgc D
        (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
        (1 : Real) eps eta0 phi
        (by
          simpa [one_mul] using (hedge_eps eta0 hKeta_eta0).1)
        (hinteg_eps eta0 hKeta_eta0).1

  have hpsiPlus_move :
      Tendsto (fun eps => ((psiPlus eps eta0).1 : SchwartzNPoint d n))
        l (nhds ((psi0).1 : SchwartzNPoint d n)) := by
    -- Checked side-test convergence, composed with subtype projection.
    exact (continuous_subtype_val.tendsto psi0).comp
      ((D.toSideZeroDiagonalCLM_tendsto_zero
        (1 : Equiv.Perm (Fin n)) (1 : Real) eta0 phi hphi_compact).mono_left
        nhdsWithin_le_nhds)

  have hBranchPlus_to_common :
      Tendsto
        (fun eps =>
          Jflat *
            integral fun u : NPointDomain d n =>
              BHW.extendF (bvt_F OS lgc n)
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
        l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    -- Ordinary OS-I `(4.1)/(4.14)` boundary-value body, written as local
    -- proof obligations rather than a named theorem.
    let Word : SchwartzNPoint d n ->L[Complex] Complex :=
      -- The selected boundary functional carried by the terminal ordinary
      -- endpoint chart.  In the literal forward-tube chart this is the
      -- continuous-linear version of `bvt_W OS lgc n`; in a retargeted
      -- metric-ball chart it is obtained from the ordinary one-branch chain
      -- by endpoint equality and identity-theorem transport.
      chainOrd.terminalBoundaryCLM

    have hOrd_sheet :
        ∀ᶠ eps in l,
          ∀ u : NPointDomain d n,
            e u + eps • eta0 ∈
              tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
            BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm
              (sourceSide (1 : Real) eps eta0 u) ∈
              BHW.ExtendedTube d n := hplus_sheet

    have hOrd_integrand_to_endpoint :
        ∀ᶠ eps in l,
          ∀ᵐ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) =
            chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
      -- This is intentionally an integrand equality, not a raw branch equality
      -- on all source points.  On the support of the moving side test, use
      -- `D.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually`
      -- to put `e u + eps • eta0` in the flat edge window, then use
      -- `hOrd_sheet` and the endpoint-centered ordinary carrier field
      -- `chainOrd.terminal_eq_ordinary_global`.  Off the moving test support,
      -- the test factor is zero.
      have hsupport :=
        D.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually
          hUsource_open (hUsource_sub_Ksource.trans hKsource_sub_P)
          Keta hKeta phi hphi_compact hphiUsource
      have hOrd_source_mem_eventually :
          ∀ᶠ eps in l, ∀ u ∈ Ksource,
            sourceSide (1 : Real) eps eta0 u ∈
              chainOrd.terminalCarrier := by
        simpa [l, sourceSide] using
          BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (1 : Real))
            (η := eta0) (K := Ksource) hKsource_compact
            chainOrd.terminalCarrier_open hOrd_endpoint_mem_on_Ksource
      filter_upwards [hsupport, hOrd_source_mem_eventually]
        with eps hsupport_eps hmem_eps
      filter_upwards with u
      by_cases hu :
          u ∈ tsupport
            ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex))
      · have hbranch :
            BHW.extendF (bvt_F OS lgc n)
                (sourceSide (1 : Real) eps eta0 u) =
              chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) := by
          have huU : u ∈ Usource :=
            (hsupport_eps eta0 hKeta_eta0).1 hu
          have huK : u ∈ Ksource := hUsource_sub_Ksource huU
          exact
            (chainOrd.terminal_eq_ordinary_global
              (sourceSide (1 : Real) eps eta0 u) (hmem_eps u huK)).symm
        rw [hbranch]
      · have hzero :
            ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 :=
          image_eq_zero_of_notMem_tsupport hu
        simp [hzero]

    have hOrd_integral_rewrite :
        ∀ᶠ eps in l,
          (integral fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (sourceSide (1 : Real) eps eta0 u) *
            ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u)) =
          (integral fun u : NPointDomain d n =>
            chainOrd.terminalBranch
              (sourceSide (1 : Real) eps eta0 u) *
            ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u)) := by
      filter_upwards [hOrd_integrand_to_endpoint] with eps heps
      exact integral_congr_ae heps

    have hOrd_fixed_psi0 :
        Tendsto
          (fun eps =>
            integral fun u : NPointDomain d n =>
              chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          l (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
      -- Important correction: this local `sourceSide` fixed leaf is only
      -- needed for the cutoff-pulled source test
      -- `psi0 = D.toZeroDiagonalCLM 1 phi`.  Do not state it for an arbitrary
      -- `SchwartzNPoint`: a general Schwartz test has no compact support, and
      -- `D.toZeroDiagonalCLM 1` does not invert an arbitrary source test.
      --
      -- The proof is the source-side quarter-turn fixed leaf for this compact
      -- `psi0`: use source-side ExtendedTube membership, zero-height endpoint
      -- DCT, and the ordinary endpoint trace.  Raw moving leaves are allowed
      -- only after a separate half-time ray identity is established.
      have hpsi0_compact :
          HasCompactSupport
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex)) := by
        simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
          using
            D.toSchwartzNPointCLM_hasCompactSupport
              (1 : Equiv.Perm (Fin n)) phi
      have hpsi0_zero_off_Ksource :
          ∀ u ∉ Ksource,
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 := by
        have hpsi0_support_Usource :
            tsupport ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex)) ⊆ Usource := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_tsupport_subset_image
                (1 : Equiv.Perm (Fin n)) phi hphiUsource
        intro u huK
        exact
          image_eq_zero_of_notMem_tsupport
            (fun hu =>
              huK (hUsource_sub_Ksource (hpsi0_support_Usource hu)))
      have hOrd_source_mem_eventually :
          ∀ᶠ eps in l, ∀ u ∈ Ksource,
            sourceSide (1 : Real) eps eta0 u ∈
              chainOrd.terminalCarrier := by
        simpa [l, sourceSide] using
          BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (1 : Real))
            (η := eta0) (K := Ksource) hKsource_compact
            chainOrd.terminalCarrier_open hOrd_endpoint_mem_on_Ksource
      have hOrd_ray_rewrite :
          ∀ᶠ eps in l,
            (integral fun u : NPointDomain d n =>
              chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)) =
            (integral fun u : NPointDomain d n =>
              BHW.extendF (bvt_F OS lgc n)
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)) := by
        filter_upwards [hOrd_source_mem_eventually] with eps hmem_eps
        apply integral_congr_ae
        filter_upwards with u
        by_cases huK : u ∈ Ksource
        · have hbranch :
              chainOrd.terminalBranch
                  (sourceSide (1 : Real) eps eta0 u) =
                BHW.extendF (bvt_F OS lgc n)
                  (sourceSide (1 : Real) eps eta0 u) :=
            chainOrd.terminal_eq_ordinary_global
              (sourceSide (1 : Real) eps eta0 u) (hmem_eps u huK)
          rw [hbranch]
        · have hzero := hpsi0_zero_off_Ksource u huK
          simp [hzero]
      have hOrd_sourceSide_fixed :
          Tendsto
            (fun eps =>
              integral fun u : NPointDomain d n =>
                BHW.extendF (bvt_F OS lgc n)
                  (sourceSide (1 : Real) eps eta0 u) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u))
            l (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
        let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
        let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n
        let pullFlatToSource :
            SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
              ->L[Complex] SchwartzNPoint d n :=
          SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
        let psi0Flat :=
          (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm)
            ((psi0).1 : SchwartzNPoint d n)
        let BranchFlatOrd : Real -> BHW.OS45FlatCommonChartReal d n -> Complex :=
          fun eps x =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun j => (x j : Complex) +
                ((eps • eta0) j : Complex) * Complex.I)
        let FlatOrd : Real -> Complex := fun eps =>
          integral fun x : BHW.OS45FlatCommonChartReal d n =>
            BranchFlatOrd eps x *
              (SCV.translateSchwartz (-(eps • eta0)) psi0Flat) x
        let SourceOrd : Real -> Complex := fun eps =>
          integral fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (sourceSide (1 : Real) eps eta0 u) *
            (((psi0).1 : SchwartzNPoint d n) u)
        obtain ⟨hpsi0Flat_compact, hpsi0Flat_edge⟩ :
            HasCompactSupport
                (psi0Flat :
                  BHW.OS45FlatCommonChartReal d n -> Complex) ∧
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
        let WordFlat :
            SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
              ->L[Complex] Complex :=
          J • (Word.comp pullFlatToSource)
        have hWordFlat_def :
            WordFlat psi0Flat =
              J * Word ((psi0).1 : SchwartzNPoint d n) := by
          have hpull :
              pullFlatToSource psi0Flat =
                ((psi0).1 : SchwartzNPoint d n) := by
            ext u
            simp [pullFlatToSource, psi0Flat]
          simp [WordFlat, hpull]
        have hflatOrd_selected :
            Tendsto (fun eps => FlatOrd eps) l
              (nhds (J * Word ((psi0).1 : SchwartzNPoint d n))) := by
          have hflatOrd_boundary :
              Tendsto (fun eps => FlatOrd eps) l
                (nhds (WordFlat psi0Flat)) := by
            -- Non-circular ordinary flat-boundary selector.
            -- 1. Use the ordinary one-branch chain to identify
            --    `BHW.os45FlatCommonChartBranch d n OS lgc 1` with the
            --    terminal ordinary branch on the compact side collar where
            --    `tsupport (translate (-(eps • eta0)) psi0Flat)` lives.
            --    The required sheet membership is the plus component of
            --    `BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually`
            --    rewritten by
            --    `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`.
            -- 2. Apply the proof-local finite selector induction for
            --    `chainOrd` to the flat test family
            --    `SCV.translateSchwartz (-(eps • eta0)) psi0Flat`, whose
            --    Schwartz limit is `psi0Flat`.
            -- 3. Rewrite the selected terminal CLM as
            --    `WordFlat psi0Flat = J * Word psi0` by the explicit CLE
            --    inverse calculation in `hWordFlat_def`.  This is the
            --    ordinary OS-I `(4.14)` flat trace; it does not use
            --    `hOrd_sourceSide_fixed`.
            have htranslateOrd :
                Tendsto
                  (fun eps : Real =>
                    SCV.translateSchwartz (-(eps • eta0)) psi0Flat)
                  l (nhds psi0Flat) := by
              have heps0 :
                  Tendsto (fun eps : Real => eps) l
                    (nhds (0 : Real)) := by
                simpa [l] using
                  (nhdsWithin_le_nhds :
                    nhdsWithin (0 : Real) (Set.Ioi 0) ≤
                      nhds (0 : Real))
              have heps :
                  Tendsto (fun eps : Real => (-eps : Real)) l
                    (nhds (0 : Real)) := heps0.neg
              simpa [smul_smul, zero_smul] using
                (SCV.tendsto_translateSchwartz_smul_nhds_of_isCompactSupport
                  eta0 psi0Flat hpsi0Flat_compact (0 : Real)).comp heps
            have hflatOrd_chain_transport :
                Tendsto (fun eps => FlatOrd eps) l
                  (nhds (WordFlat psi0Flat)) := by
              -- Proof-local finite-chain boundary transport.
              -- Base: the ordinary `(4.1)` seed has the OS-I fixed/moving
              -- boundary value for every compact flat test after pulling the
              -- real edge through `pullFlatToSource`; the selected fixed
              -- value is `WordFlat`.
              -- Step: for each adjacent pair of metric-ball charts in
              -- `chainOrd`, the checked local seed edge gives equality of the
              -- two holomorphic branches at one lifted side point in the
              -- pointed overlap.  Compactness of the unshifted flat support
              -- and continuity of that side lift give a uniform collar, so
              -- the two side integrals are eventually equal by
              -- `integral_congr_ae`.  Uniqueness of limits transports the
              -- selected CLM to the next chart.
              -- End: the terminal chart is the flat plus chart
              -- `BHW.os45FlatCommonChartOmega d n 1`; the finite induction
              -- gives the displayed terminal flat boundary value.  This is an
              -- in-body induction over `chainOrd`, not a public wrapper.
              -- Inline the `hOrd_base_selected` / `hOrd_chain_step` /
              -- `hOrd_chain_selected` block from "Flat Boundary Selector
              -- Induction" below.  Do not call or add a
              -- `terminal_flatBoundaryValue_translatedTest_of_chain` field.
              exact hOrd_flatBoundary_from_inline_chain
            exact hflatOrd_chain_transport
          simpa [hWordFlat_def] using hflatOrd_boundary
        have hintegOrd_for_cancel :
            ∀ᶠ eps in l,
              Integrable
                (fun x : BHW.OS45FlatCommonChartReal d n =>
                  BHW.os45FlatCommonChartBranch d n OS lgc
                    (1 : Equiv.Perm (Fin n))
                    (fun j =>
                      ((x + eps • eta0) j : Complex) +
                        ((eps • eta0) j : Complex) * Complex.I) *
                  (SCV.translateSchwartz (-(eps • eta0)) psi0Flat)
                    (x + eps • eta0)) := by
          filter_upwards [hpsi0Flat_integ] with eps hinteg_eps
          exact (hinteg_eps eta0 hKeta_eta0).1
        have hsource_from_flat :
            Tendsto
              (fun eps : Real =>
                integral fun u : NPointDomain d n =>
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.permAct (d := d)
                      ((1 : Equiv.Perm (Fin n)).symm)
                      (sourceSide (1 : Real) eps eta0 u)) *
                  psi0Flat
                    (BHW.os45CommonEdgeFlatCLE d n
                      (1 : Equiv.Perm (Fin n)) u))
              l (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
          exact
            BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest
              (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
              (1 : Real) eta0 psi0Flat
              hintegOrd_for_cancel hflatOrd_selected
        have hsource_rewrite :
            (fun eps : Real =>
              integral fun u : NPointDomain d n =>
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d)
                    ((1 : Equiv.Perm (Fin n)).symm)
                    (sourceSide (1 : Real) eps eta0 u)) *
                psi0Flat
                  (BHW.os45CommonEdgeFlatCLE d n
                    (1 : Equiv.Perm (Fin n)) u))
            =ᶠ[l] (fun eps : Real => SourceOrd eps) := by
          filter_upwards with eps
          apply integral_congr_ae
          filter_upwards with u
          have hpull_eval :
              psi0Flat
                  (BHW.os45CommonEdgeFlatCLE d n
                    (1 : Equiv.Perm (Fin n)) u) =
                (((psi0).1 : SchwartzNPoint d n) u) := by
            have hpull :
                pullFlatToSource psi0Flat =
                  ((psi0).1 : SchwartzNPoint d n) := by
              ext v
              simp [pullFlatToSource, psi0Flat]
            simpa [pullFlatToSource] using congrArg (fun f => f u) hpull
          simp [SourceOrd, sourceSide, hpull_eval]
        exact hsource_from_flat.congr' hsource_rewrite
      exact hOrd_sourceSide_fixed.congr' hOrd_ray_rewrite.symm

    have hOrd_moving :
        Tendsto
          (fun eps =>
            integral fun u : NPointDomain d n =>
              chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          l (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
      -- Use the compact-support moving-test perturbation, not a public wrapper.
      -- The fixed-test leaf gives the compact specialization
      -- `hOrd_fixed_psi0`.  The checked
      -- SourceSide compact-collar bound gives, after shrinking `l`,
      -- `Msource` and a compact `Ksource` containing the supports of
      -- `((psiPlus eps eta0).1)` and `((psi0).1)` such that
      --
      --   ∀ u ∈ Ksource,
      --     ‖chainOrd.terminalBranch (sourceSide 1 eps eta0 u)‖ ≤ Msource.
      --
      -- The common-support input is now checked for the concrete Figure-2-4
      -- side family by
      -- `D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually`,
      -- applied to the current flat test `phi`, the source window
      -- `Usource ⊆ Ksource`, and `{eta0}`.  The
      -- zeroth-seminorm input is checked by
      -- `D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero`,
      -- restricted from `𝓝 0` to `l = 𝓝[Set.Ioi 0] 0`.  The compact-support
      -- perturbation theorem then adds a zero error to
      -- `hOrd_fixed_psi0`.
      -- Lean update: the current Hdiff holes should not call the moving-test
      -- support theorem as though it selected the Schwinger value.  First prove
      -- the fixed-test selected limit by the flat one-branch selector, prove the
      -- fixed-test endpoint DCT, and identify that endpoint with the selected
      -- value by `tendsto_nhds_unique`; then rewrite the already-present moving
      -- endpoint DCT.  If this chain-terminal audit expansion is used instead,
      -- the `hOrd_source_test_diff_zero`/`hsplit` block below is the checked
      -- theorem body for moving the test after `hOrd_fixed_psi0`.
      have hpsi0_zero_off_Ksource :
          ∀ u ∉ Ksource,
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 := by
        have hpsi0_support_Usource :
            tsupport ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex)) ⊆ Usource := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_tsupport_subset_image
                (1 : Equiv.Perm (Fin n)) phi hphiUsource
        intro u huK
        exact
          image_eq_zero_of_notMem_tsupport
            (fun hu =>
              huK (hUsource_sub_Ksource (hpsi0_support_Usource hu)))
      have hpsiPlus_commonCompactSupport :
          ∀ᶠ eps in l, ∀ u ∉ Ksource,
            ((((psiPlus eps eta0).1 : SchwartzNPoint d n) -
              ((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 := by
        have hpack :=
          D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually
            hUsource_open hUsource_sub_Ksource ({eta0}) isCompact_singleton
            phi hphi_compact hphiUsource
        filter_upwards [hpack] with eps hpack_eps u huK
        simpa [l, psiPlus, psi0, Pi.sub_apply] using
          (hpack_eps eta0 (by simp)).1 u huK
      have hpsiPlus_seminorm0_tendsto :
          Tendsto
            (fun eps : Real =>
              SchwartzMap.seminorm Real 0 0
                (((psiPlus eps eta0).1 : SchwartzNPoint d n) -
                  ((psi0).1 : SchwartzNPoint d n)))
            l (nhds 0) := by
        exact
          (D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero
            (1 : Equiv.Perm (Fin n)) (1 : Real) eta0
            phi hphi_compact).mono_left nhdsWithin_le_nhds
      have hOrd_source_test_diff_zero :
          Tendsto
            (fun eps =>
              integral fun u : NPointDomain d n =>
                chainOrd.terminalBranch
                  (sourceSide (1 : Real) eps eta0 u) *
                ((((psiPlus eps eta0).1 : SchwartzNPoint d n) -
                  ((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u))
            l (nhds 0) := by
        -- Checked neutral analytic support:
        -- `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport`
        -- with `ρperm = 1`, `sgn = 1`, `eps := fun eps => eps`,
        -- `F := chainOrd.terminalBranch`, and `K := Ksource`.
        -- Inputs are the terminal ordinary carrier openness/continuity, endpoint
        -- membership on `Ksource`, and the checked side-test support/seminorm
        -- facts above.
        exact
          BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := 1) (η := eta0)
            chainOrd.terminalCarrier_open
            chainOrd.terminalBranch_continuousOn
            hKsource_compact hOrd_endpoint_mem_on_Ksource
            (eps := fun eps : Real => eps) (by simpa [l] using tendsto_id)
            hpsiPlus_commonCompactSupport hpsiPlus_seminorm0_tendsto
      obtain ⟨MsourceOrd, _hMsourceOrd_nonneg,
          hOrd_source_bound_eventually_raw⟩ :=
        BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
          (ρperm := (1 : Equiv.Perm (Fin n)))
          (sgn := (1 : Real)) (η := eta0)
          (K := Ksource) hKsource_compact
          chainOrd.terminalCarrier_open hOrd_endpoint_mem_on_Ksource
          chainOrd.terminalBranch_continuousOn
      have hOrd_source_bound_eventually :
          ∀ᶠ eps in l, ∀ u ∈ Ksource,
            ‖chainOrd.terminalBranch
              (sourceSide (1 : Real) eps eta0 u)‖ ≤ MsourceOrd := by
        simpa [l, sourceSide] using hOrd_source_bound_eventually_raw
      have hOrd_source_mem_eventually :
          ∀ᶠ eps in l, ∀ u ∈ Ksource,
            sourceSide (1 : Real) eps eta0 u ∈
              chainOrd.terminalCarrier := by
        simpa [l, sourceSide] using
          BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (1 : Real))
            (η := eta0) (K := Ksource) hKsource_compact
            chainOrd.terminalCarrier_open hOrd_endpoint_mem_on_Ksource
      have hsplit :
          (fun eps =>
            integral fun u : NPointDomain d n =>
              chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          =ᶠ[l]
          (fun eps =>
            (integral fun u : NPointDomain d n =>
              chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)) +
            (integral fun u : NPointDomain d n =>
              chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) -
                ((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))) := by
        -- Inline algebra: eventually both moving and fixed tests are supported
        -- in the same compact set.  Get the compact-collar membership and
        -- branch bound once, then use
        -- `BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport`
        -- inside the `filter_upwards` block with `ψ = (psi0).1` and
        -- `ψ = (psiPlus eps eta0).1 - (psi0).1`.
        -- Lean body:
        --   filter_upwards [hpsiPlus_commonCompactSupport,
        --     hOrd_source_mem_eventually, hOrd_source_bound_eventually]
        --     with eps hsupp hmem_eps hbound_eps
        --   have hfixed_int :=
        --     BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
        --       (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := 1)
        --       (eps := eps) (η := eta0)
        --       chainOrd.terminalBranch_continuousOn hKsource_compact
        --       hmem_eps hbound_eps ((psi0).1 : SchwartzNPoint d n)
        --       hpsi0_zero_off_Ksource
        --   have hdiff_int :=
        --     BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
        --       (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := 1)
        --       (eps := eps) (η := eta0)
        --       chainOrd.terminalBranch_continuousOn hKsource_compact
        --       hmem_eps hbound_eps
        --       (((psiPlus eps eta0).1 : SchwartzNPoint d n) -
        --         ((psi0).1 : SchwartzNPoint d n))
        --       (fun u huK => hsupp u huK)
        --   rw [← MeasureTheory.integral_add hfixed_int hdiff_int]
        --   apply integral_congr_ae
        --   filter_upwards with u
        --   simp [Pi.sub_apply, sub_eq_add_neg, mul_add, add_comm,
        --     add_left_comm, add_assoc]
      exact (hOrd_fixed_psi0.add hOrd_source_test_diff_zero).congr' hsplit.symm

    have hOrd_boundary_to_source :
        Word ((psi0).1 : SchwartzNPoint d n) =
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) := by
      have hOrd_endpoint_limit :
          Tendsto
            (fun eps =>
              integral fun u : NPointDomain d n =>
                chainOrd.terminalBranch
                  (sourceSide (1 : Real) eps eta0 u) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u))
            l
            (nhds
              (∫ u : NPointDomain d n,
                chainOrd.terminalBranch
                  (sourceSide (1 : Real) 0 eta0 u) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u))) := by
        have hpsi0_compact :
            HasCompactSupport
              (((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_hasCompactSupport
                (1 : Equiv.Perm (Fin n)) phi
        have hpsi0_support_V :
            tsupport
              (((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) ⊆ P.V := by
          -- `psi0 = D.toZeroDiagonalCLM 1 phi`; use the checked source
          -- cutoff support theorem
          -- `D.toSchwartzNPointCLM_tsupport_subset_V 1 phi hphiE`.
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_tsupport_subset_V
                (1 : Equiv.Perm (Fin n)) phi hphiE
        have hOrd_endpoint_mem :
            ∀ u ∈ tsupport
                (((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex),
              sourceSide (1 : Real) 0 eta0 u ∈
                chainOrd.terminalCarrier := by
          intro u hu
          have huV : u ∈ P.V := hpsi0_support_V hu
          have hzero :
              sourceSide (1 : Real) 0 eta0 u =
                BHW.os45QuarterTurnConfig
                  (fun k => wickRotatePoint (u k)) := by
            simpa [sourceSide]
              using
                BHW.os45FlatCommonChartSourceSide_zero
                  (d := d) (n := n)
                  (ρperm := (1 : Equiv.Perm (Fin n)))
                  (sgn := (1 : Real)) (η := eta0) (u := u)
          have hwindow :
              BHW.os45QuarterTurnConfig
                  (fun k => wickRotatePoint (u k)) ∈
                chainOrd.terminalCarrier := by
            -- This is the endpoint-centered ordinary common-edge window field
            -- exported by the one-branch chain.  It is built from
            -- `H.ordinaryCommonEdge_metricBallChartInWindow` and `huV`.
            exact chainOrd.terminal_contains_ordinaryCommonEdge u huV
          simpa [hzero] using hwindow
        have hOrd_eventual_collar :
            ∀ᶠ eps in l,
              ∀ u ∈ tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex),
                sourceSide (1 : Real) eps eta0 u ∈
                  chainOrd.terminalCarrier := by
          exact
            BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
              (ρperm := (1 : Equiv.Perm (Fin n)))
              (sgn := (1 : Real)) (η := eta0)
              (K :=
                tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex))
              hpsi0_compact.isCompact
              chainOrd.terminalCarrier_open
              hOrd_endpoint_mem
        have hOrd_pointwise :
            ∀ u : NPointDomain d n,
              Tendsto
                (fun eps =>
                  chainOrd.terminalBranch
                    (sourceSide (1 : Real) eps eta0 u) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u))
                l
                (nhds
                  (chainOrd.terminalBranch
                    (sourceSide (1 : Real) 0 eta0 u) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u))) := by
          intro u
          by_cases hu :
              u ∈ tsupport
                (((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex)
          · have hbranch_tendsto :
                Tendsto
                  (fun eps : Real =>
                    chainOrd.terminalBranch
                      (sourceSide (1 : Real) eps eta0 u))
                  l
                  (nhds
                    (chainOrd.terminalBranch
                      (sourceSide (1 : Real) 0 eta0 u))) := by
              exact
                BHW.tendsto_comp_os45FlatCommonChartSourceSide_nhdsWithin
                  (d := d) (n := n)
                  (ρperm := (1 : Equiv.Perm (Fin n)))
                  (sgn := (1 : Real)) (η := eta0) (u := u)
                  chainOrd.terminalCarrier_open
                  chainOrd.terminalBranch_continuousOn
                  (hOrd_endpoint_mem u hu)
            exact hbranch_tendsto.mul tendsto_const_nhds
          · -- Off support, the test factor is zero, so the product is
            -- eventually and at the endpoint identically zero.
            have hzero :
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) = 0 :=
              image_eq_zero_of_notMem_tsupport hu
            simpa [hzero]
        have hOrd_bound :
            ∃ g : NPointDomain d n -> Real,
              Integrable g ∧
              ∀ᶠ eps in l,
                ∀ᵐ u : NPointDomain d n,
                  ‖chainOrd.terminalBranch
                    (sourceSide (1 : Real) eps eta0 u) *
                    ((((psi0).1 : SchwartzNPoint d n) :
                      NPointDomain d n -> Complex) u)‖ ≤ g u := by
          rcases
            BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
              (ρperm := (1 : Equiv.Perm (Fin n)))
              (sgn := (1 : Real)) (η := eta0)
              (K :=
                tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex))
              hpsi0_compact.isCompact
              chainOrd.terminalCarrier_open
              hOrd_endpoint_mem
              chainOrd.terminalBranch_continuousOn with
            ⟨MOrd, hMOrd_nonneg, hMOrd_bound⟩
          refine ⟨
            fun u : NPointDomain d n =>
              MOrd *
                ‖((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u)‖,
            ?_, ?_⟩
          · have hpsi0_integrable :
                Integrable
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex)) := by
              simpa using
                (SchwartzMap.integrable
                  ((psi0).1 : SchwartzNPoint d n))
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (hpsi0_integrable.norm.const_mul MOrd)
          · filter_upwards [hMOrd_bound] with eps hMord
            filter_upwards with u
            by_cases hu :
                u ∈ tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex)
            · calc
                ‖chainOrd.terminalBranch
                    (sourceSide (1 : Real) eps eta0 u) *
                    ((((psi0).1 : SchwartzNPoint d n) :
                      NPointDomain d n -> Complex) u)‖
                    = ‖chainOrd.terminalBranch
                        (sourceSide (1 : Real) eps eta0 u)‖ *
                      ‖((((psi0).1 : SchwartzNPoint d n) :
                        NPointDomain d n -> Complex) u)‖ := by
                        simp [norm_mul]
                _ ≤ MOrd *
                      ‖((((psi0).1 : SchwartzNPoint d n) :
                        NPointDomain d n -> Complex) u)‖ :=
                    mul_le_mul_of_nonneg_right (hMord u hu) (norm_nonneg _)
            · have hzero :
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u) = 0 :=
                image_eq_zero_of_notMem_tsupport hu
              simp [hzero, hMOrd_nonneg]
        rcases hOrd_bound with ⟨g, hg_int, hg_bound⟩
        have hOrd_aestrongly :
            ∀ᶠ eps in l,
              AEStronglyMeasurable
                (fun u : NPointDomain d n =>
                  chainOrd.terminalBranch
                    (sourceSide (1 : Real) eps eta0 u) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u)) := by
          filter_upwards [hOrd_eventual_collar] with eps heps
          let K : Set (NPointDomain d n) :=
            tsupport
              (((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex)
          let f : NPointDomain d n -> Complex := fun u =>
            chainOrd.terminalBranch
              (sourceSide (1 : Real) eps eta0 u) *
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u)
          have hK_compact : IsCompact K := hpsi0_compact.isCompact
          have hsource_cont :
              Continuous fun u : NPointDomain d n =>
                sourceSide (1 : Real) eps eta0 u := by
            simpa [sourceSide]
              using
                BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
                  (d := d) (n := n)
                  (ρperm := (1 : Equiv.Perm (Fin n)))
                  (sgn := (1 : Real)) (eps := eps) (η := eta0)
          have hbranch_cont_on_K :
              ContinuousOn
                (fun u : NPointDomain d n =>
                  chainOrd.terminalBranch
                    (sourceSide (1 : Real) eps eta0 u)) K := by
            exact
              chainOrd.terminalBranch_continuousOn.comp
                hsource_cont.continuousOn heps
          have htest_cont :
              Continuous
                (((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) :=
            ((psi0).1 : SchwartzNPoint d n).continuous
          have hzero_off :
              ∀ u ∉ K, f u = 0 := by
            intro u hu
            have hzero :
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) = 0 :=
              image_eq_zero_of_notMem_tsupport hu
            simp [f, hzero]
          exact
            BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport
              (K := K) hK_compact
              hbranch_cont_on_K htest_cont.continuousOn hzero_off
        apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (bound := g)
        · -- AEStronglyMeasurable of the terminal-branch integrand from
          -- continuity on the eventual collar and zero off compact support.
          exact hOrd_aestrongly
        · -- Domination by the polynomial collar majorant.
          exact hg_bound
        · -- The majorant is integrable.
          exact hg_int
        · -- Pointwise convergence.
          intro u
          exact hOrd_pointwise u
      have hOrd_endpoint_as_source :
          (∫ u : NPointDomain d n,
              chainOrd.terminalBranch
                (sourceSide (1 : Real) 0 eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)) =
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
        have hpsi0_support_V :
            tsupport
              (((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) ⊆ P.V := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_tsupport_subset_V
                (1 : Equiv.Perm (Fin n)) phi hphiE
        have hOrd_endpoint_as_carrier :
            (∫ u : NPointDomain d n,
                chainOrd.terminalBranch
                    (sourceSide (1 : Real) 0 eta0 u) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u)) =
              ∫ u : NPointDomain d n,
                bvt_F OS lgc n
                    (BHW.os45QuarterTurnConfig
                      (fun k => wickRotatePoint (u k))) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u) := by
          have hOrd_endpoint_pointwise :
            ∀ᵐ u : NPointDomain d n,
              chainOrd.terminalBranch
                  (sourceSide (1 : Real) 0 eta0 u) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) =
              bvt_F OS lgc n
                  (BHW.os45QuarterTurnConfig
                    (fun k => wickRotatePoint (u k))) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) := by
            filter_upwards with u
            by_cases hu :
                u ∈ tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex)
            · have huV : u ∈ P.V := hpsi0_support_V hu
              have hsource_zero :
                  sourceSide (1 : Real) 0 eta0 u =
                    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                      (BHW.realEmbed
                        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) u)) := by
                simpa [sourceSide] using
                  BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
                    (d := d) (n := n)
                    (ρperm := (1 : Equiv.Perm (Fin n)))
                    (sgn := (1 : Real)) (η := eta0) (u := u)
              have hbranch :
                  chainOrd.terminalBranch
                      (sourceSide (1 : Real) 0 eta0 u) =
                    BHW.extendF (bvt_F OS lgc n)
                      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                        (BHW.realEmbed
                          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                            (1 : Equiv.Perm (Fin n)) u))) := by
                -- Terminal ordinary branch equality at the endpoint-centered
                -- chart, using `chainOrd.terminal_eq_ordinary_global`.
                simpa [hsource_zero] using
                  chainOrd.terminal_eq_ordinary_global
                    (sourceSide (1 : Real) 0 eta0 u)
              have hcarrier :
                  ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                    (BHW.realEmbed
                      (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                        (1 : Equiv.Perm (Fin n)) u))) =
                    BHW.os45QuarterTurnConfig
                      (fun k => wickRotatePoint (u k)) := by
                -- Coordinate carrier identity only.  This is the inverse
                -- quarter-turn of the real common edge, not the unturned Wick
                -- point.
                exact
                  BHW.os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick
                    (d := d) (n := n)
                    (ρperm := (1 : Equiv.Perm (Fin n))) (u := u)
              have hraw_forward :
                  BHW.extendF (bvt_F OS lgc n)
                      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                        (BHW.realEmbed
                          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                            (1 : Equiv.Perm (Fin n)) u))) =
                    bvt_F OS lgc n
                      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                        (BHW.realEmbed
                          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                            (1 : Equiv.Perm (Fin n)) u))) := by
                exact
                  BHW.os45Figure24CommonEdge_ordinary_extendF_eq_bvt_F
                    (d := d) hd OS lgc (P := P) huV
              rw [hbranch, hraw_forward, hcarrier]
            · have hzero :
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u) = 0 :=
                image_eq_zero_of_notMem_tsupport hu
              simp [hzero]
          exact integral_congr_ae hOrd_endpoint_pointwise
        have hOrd_carrier_pairing :
            (∫ u : NPointDomain d n,
                bvt_F OS lgc n
                    (BHW.os45QuarterTurnConfig
                      (fun k => wickRotatePoint (u k))) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u)) =
              ∫ u : NPointDomain d n,
                bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u) := by
          let e := BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n))
          let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n
          let psi0Flat :=
            (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm)
              ((psi0).1 : SchwartzNPoint d n)
          let pullFlatToSource :
              SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
                ->L[Complex] SchwartzNPoint d n :=
            SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
          let carrierPairing : Complex :=
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n
                  (BHW.os45QuarterTurnConfig
                    (fun k => wickRotatePoint (u k))) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u)
          let wickPairing : Complex :=
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u)
          let WordFlat :
              SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
                ->L[Complex] Complex :=
            J • (Word.comp pullFlatToSource)
          have hJ_ne : J ≠ 0 := by
            exact
              Complex.ofReal_ne_zero.mpr
                (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
          have hWord_carrier :
              WordFlat psi0Flat = J * carrierPairing := by
            -- Proof-local transcript:
            -- 1. `pullFlatToSource psi0Flat = psi0` by the CLE inverse
            --    calculation, then `simp [WordFlat]` reduces the left side to
            --    `J * Word psi0`.
            -- 2. `hWord_endpoint` identifies `Word psi0` with the
            --    zero-height source-side endpoint integral.
            -- 3. `hOrd_endpoint_as_carrier` rewrites that endpoint integral to
            --    `carrierPairing`, using
            --    `BHW.os45FlatCommonChartSourceSide_zero`,
            --    `chainOrd.terminal_eq_ordinary_global`, and
            --    `BHW.os45Figure24CommonEdge_ordinary_extendF_eq_bvt_F` on
            --    `tsupport psi0`.
            -- 4. The off-support part is killed by
            --    `image_eq_zero_of_notMem_tsupport`.
            calc
              WordFlat psi0Flat = J * Word ((psi0).1 : SchwartzNPoint d n) := by
                have hpull :
                    pullFlatToSource psi0Flat =
                      ((psi0).1 : SchwartzNPoint d n) := by
                  ext u
                  simp [pullFlatToSource, psi0Flat]
                simp [WordFlat, hpull]
              _ = J * carrierPairing := by
                rw [hWord_endpoint, hOrd_endpoint_as_carrier]
          have hWord_wick :
              WordFlat psi0Flat = J * wickPairing := by
            -- Proof-local transcript:
            -- 1. reduce again to `J * Word psi0`;
            -- 2. use the ordinary Wick trace transported by `chainOrd` to get
            --    `Word psi0 = OS.S n (D.toZeroDiagonalCLM 1 phi)`;
            -- 3. rewrite `wickPairing` to the same Schwinger value with
            --    `bvt_euclidean_restriction` and the definitional equality
            --    between `psi0` and `D.toZeroDiagonalCLM 1 phi`.
            have hWord_schwinger :
                Word ((psi0).1 : SchwartzNPoint d n) =
                  OS.S n (D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) phi) := by
              -- Ordinary `(4.1)` Wick trace, transported along `chainOrd`.
              exact hOrd_currentTest_schwinger
            have hwick_schwinger :
                wickPairing =
                  OS.S n (D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) phi) := by
              -- This is the checked Euclidean restriction for the same
              -- zero-diagonal test, unfolded through `psi0`.
              simpa [wickPairing, psi0] using
                (bvt_euclidean_restriction (d := d) OS lgc n
                  (D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) phi)).symm
            calc
              WordFlat psi0Flat = J * Word ((psi0).1 : SchwartzNPoint d n) := by
                have hpull :
                    pullFlatToSource psi0Flat =
                      ((psi0).1 : SchwartzNPoint d n) := by
                  ext u
                  simp [pullFlatToSource, psi0Flat]
                simp [WordFlat, hpull]
              _ = J * wickPairing := by
                rw [hWord_schwinger, hwick_schwinger]
          have hmul : J * carrierPairing = J * wickPairing :=
            hWord_carrier.symm.trans hWord_wick
          exact mul_left_cancel₀ hJ_ne hmul
        exact hOrd_endpoint_as_carrier.trans hOrd_carrier_pairing
      have hWord_endpoint :
          Word ((psi0).1 : SchwartzNPoint d n) =
            ∫ u : NPointDomain d n,
              chainOrd.terminalBranch
                (sourceSide (1 : Real) 0 eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
        exact tendsto_nhds_unique hOrd_fixed_psi0 hOrd_endpoint_limit
      exact hWord_endpoint.trans hOrd_endpoint_as_source

    have hOrd_source_norm :
        Word ((psi0).1 : SchwartzNPoint d n) =
          OS.S n (D.toZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) phi) := by
      calc
        Word ((psi0).1 : SchwartzNPoint d n)
            = ∫ u : NPointDomain d n,
                bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) :=
              hOrd_boundary_to_source
        _ = OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi) := by
              -- `psi0` is definitionally
              -- `D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi`.
              simpa [psi0] using
                (bvt_euclidean_restriction (d := d) OS lgc n
                  (D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) phi)).symm

    have hOrd_as_extendF :
        Tendsto
          (fun eps =>
            integral fun u : NPointDomain d n =>
              BHW.extendF (bvt_F OS lgc n)
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          l
          (nhds
            (OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
      exact hOrd_moving.congr' hOrd_integral_rewrite.symm |>.congr
        (by simpa [hOrd_source_norm])

    exact hOrd_as_extendF.const_mul Jflat

  have hSourcePlus_eta0 :
      Tendsto (fun eps => SourcePlusSide eps eta0) l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    exact (hSourcePlus_common.tendsto hKeta_eta0)

  have hbranch :
      Tendsto (fun eps => BranchPlusSide eps eta0) l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    exact hBranchPlus_to_common.congr' hplus_pullback.symm

  exact hbranch.sub hSourcePlus_eta0 |>.congr'
    (by filter_upwards with eps; ring_nf)

have hPlus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      l Keta := by
  simpa [Keta] using
    (SCV.tendstoUniformlyOn_singleton_iff_tendsto
      (F := fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
      (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (p := l) (x := eta0)).2 hPlus_asymptotic_eta0

have hMinus_asymptotic_eta0 :
    Tendsto
      (fun eps => BranchMinusSide eps eta0 - SourceMinusSide eps eta0)
      l (nhds (0 : Complex)) := by
  have hminus_sheet :
      ∀ᶠ eps in l,
        ∀ u : NPointDomain d n,
          e u + (-eps : Real) • eta0 ∈
            tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
          BHW.permAct (d := d) (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
            (sourceSide (-1 : Real) eps eta0 u) ∈
            BHW.ExtendedTube d n := by
    -- Same checked sheet packet, now selecting the raw-adjacent minus sheet.
    have hsheet :=
      BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually
        (d := d) hd (P := P) Keta hKeta hKetaC
        phi hphi_compact hphiE
    filter_upwards [hsheet] with eps heps u hu
    exact (heps eta0 hKeta_eta0).2 u hu

  have hminus_pullback :
      ∀ᶠ eps in l,
        BranchMinusSide eps eta0 =
          Jflat *
            integral fun u : NPointDomain d n =>
              Badj_terminal (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
    -- Use the same checked branch/source pullback with
    -- `σ = P.τ.symm * 1`, then rewrite the resulting `extendF` value to the
    -- terminal adjacent branch only after raw `(4.12)` provenance has reached
    -- the endpoint chart.
    have hinteg :=
      BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
        (d := d) hd OS lgc (P := P) Keta hKeta hKetaC
        phi hphi_compact hphiE
    obtain ⟨rEdge, hrEdge_pos, hEdge⟩ :=
      BHW.os45FlatCommonChart_sideSupport_radius
        (d := d) (P := P) Keta hKeta hKetaC
        phi hphi_compact hphiE
    have hedge_eventually :
        ∀ᶠ eps in l, ∀ eta ∈ Keta,
          tsupport (SCV.translateSchwartz (eps • eta) phi :
            BHW.OS45FlatCommonChartReal d n -> Complex) <=
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) ∧
          tsupport (SCV.translateSchwartz ((-eps : Real) • eta) phi :
            BHW.OS45FlatCommonChartReal d n -> Complex) <=
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) := by
      filter_upwards
        [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds hrEdge_pos)]
        with eps heps_pos heps_lt eta heta
      exact hEdge eps heps_pos heps_lt eta heta
    have hsupport :=
      D.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually
        hUsource_open (hUsource_sub_Ksource.trans hKsource_sub_P)
        Keta hKeta phi hphi_compact hphiUsource
    have hAdj_source_mem_eventually :
        ∀ᶠ eps in l, ∀ u ∈ Ksource,
          sourceSide (-1 : Real) eps eta0 u ∈
            chainAdj.terminalCarrier := by
      simpa [l, sourceSide] using
        BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
          (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (-1 : Real))
          (η := eta0) (K := Ksource) hKsource_compact
          chainAdj.terminalCarrier_open hAdj_endpoint_mem_on_Ksource
    filter_upwards [hinteg, hedge_eventually, hsupport,
      hAdj_source_mem_eventually, hAdj_terminal_eq_endpoint_eventually]
      with eps hinteg_eps hedge_eps hsupport_eps hmem_eps hterminal_eps
    have hraw_pullback :=
      BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
        (d := d) hd OS lgc D
        (P.τ.symm * (1 : Equiv.Perm (Fin n))) (1 : Equiv.Perm (Fin n))
        (-1 : Real) eps eta0 phi
        (by
          simpa [neg_mul, one_mul] using (hedge_eps eta0 hKeta_eta0).2)
        (hinteg_eps eta0 hKeta_eta0).2
    have hterminal_ae :
        (fun u : NPointDomain d n =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (sourceSide (-1 : Real) eps eta0 u)) *
          ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u))
        =ᵐ[volume]
        (fun u : NPointDomain d n =>
          Badj_terminal (sourceSide (-1 : Real) eps eta0 u) *
          ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u)) := by
      filter_upwards with u
      by_cases hu :
          u ∈ tsupport
            ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex))
      · have huU : u ∈ Usource :=
          (hsupport_eps eta0 hKeta_eta0).2.1 hu
        have huK : u ∈ Ksource := hUsource_sub_Ksource huU
        have hcarrier := hmem_eps u huK
        have hbranch := hterminal_eps eta0 hKeta_eta0 u hu hcarrier
        rw [hbranch]
      · have hzero :
            ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 :=
          image_eq_zero_of_notMem_tsupport hu
        simp [hzero]
    exact hraw_pullback.trans
      (congrArg (fun I : Complex => Jflat * I)
        (integral_congr_ae hterminal_ae))

  have hpsiMinus_move :
      Tendsto (fun eps => ((psiMinus eps eta0).1 : SchwartzNPoint d n))
        l (nhds ((psi0).1 : SchwartzNPoint d n)) := by
    exact (continuous_subtype_val.tendsto psi0).comp
      ((D.toSideZeroDiagonalCLM_tendsto_zero
        (1 : Equiv.Perm (Fin n)) (-1 : Real) eta0 phi hphi_compact).mono_left
        nhdsWithin_le_nhds)

  have hBranchMinus_to_common :
      Tendsto
        (fun eps =>
          Jflat *
            integral fun u : NPointDomain d n =>
              Badj_terminal (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
        l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    -- Raw-adjacent OS-I `(4.12)/(4.14)` boundary-value body, also kept as
    -- local proof obligations.
    let Wadj : SchwartzNPoint d n ->L[Complex] Complex :=
      -- The selected boundary functional transported from the genuine
      -- `OmegaSeed412/BSeed412` analytic element to the terminal adjacent
      -- endpoint chart.  It is not the downstream deterministic adjacent
      -- datum used as an initial branch.
      chainAdj.terminalBoundaryCLM

    have hAdj_sheet :
        ∀ᶠ eps in l,
          ∀ u : NPointDomain d n,
            e u + (-eps : Real) • eta0 ∈
              tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
            BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (sourceSide (-1 : Real) eps eta0 u) ∈
              BHW.ExtendedTube d n := hminus_sheet

    have hAdj_integrand_to_endpoint :
        ∀ᶠ eps in l,
          ∀ᵐ u : NPointDomain d n,
            Badj_terminal (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) =
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
      -- This integrand equality is again needed only on the support of the moving
      -- minus-side test.  The adjacent incoming sheet is the raw `(4.12)` window
      -- `{z | BHW.permAct P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ` with branch
      -- `BSeed412 z = bvt_F OS lgc n (BHW.permAct P.τ z)`.  The outgoing flat
      -- side is `BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)`.  Use the
      -- retained adjacent one-branch chain to reach the terminal endpoint, then
      -- use endpoint equality only on this terminal chart.
      have hsupport :=
        D.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually
          hUsource_open (hUsource_sub_Ksource.trans hKsource_sub_P)
          Keta hKeta phi hphi_compact hphiUsource
      have hAdj_source_mem_eventually :
          ∀ᶠ eps in l, ∀ u ∈ Ksource,
            sourceSide (-1 : Real) eps eta0 u ∈
              chainAdj.terminalCarrier := by
        simpa [l, sourceSide] using
          BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (-1 : Real))
            (η := eta0) (K := Ksource) hKsource_compact
            chainAdj.terminalCarrier_open hAdj_endpoint_mem_on_Ksource
      filter_upwards [hsupport, hAdj_source_mem_eventually,
        hAdj_terminal_eq_endpoint_eventually]
        with eps hsupport_eps hmem_eps hterminal_eps
      filter_upwards with u
      by_cases hu :
          u ∈ tsupport
            ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex))
      · have huU : u ∈ Usource :=
          (hsupport_eps eta0 hKeta_eta0).2.1 hu
        have huK : u ∈ Ksource := hUsource_sub_Ksource huU
        have hcarrier := hmem_eps u huK
        have hbranch := hterminal_eps eta0 hKeta_eta0 u hu hcarrier
        rw [hbranch]
      · have hzero :
            ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 :=
          image_eq_zero_of_notMem_tsupport hu
        simp [hzero]

    have hAdj_integral_rewrite :
        ∀ᶠ eps in l,
          (integral fun u : NPointDomain d n =>
            Badj_terminal (sourceSide (-1 : Real) eps eta0 u) *
            ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u)) =
          (integral fun u : NPointDomain d n =>
            chainAdj.terminalBranch
              (sourceSide (-1 : Real) eps eta0 u) *
            ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u)) := by
      filter_upwards [hAdj_integrand_to_endpoint] with eps heps
      exact integral_congr_ae heps

    have hAdj_fixed_psi0 :
        Tendsto
          (fun eps =>
            integral fun u : NPointDomain d n =>
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) eps eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          l (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
      -- Adjacent correction parallel to the ordinary side: the local
      -- `sourceSide` fixed leaf is only the compact cutoff-pulled
      -- specialization `psi0`.  The all-Schwartz theorem is the raw `(4.12)`
      -- tube boundary theorem before CLE/source pullback.  Do not state a
      -- post-pullback local carrier theorem for arbitrary Schwartz tests.
      have hpsi0_compact :
          HasCompactSupport
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex)) := by
        simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
          using
            D.toSchwartzNPointCLM_hasCompactSupport
              (1 : Equiv.Perm (Fin n)) phi
      have hpsi0_zero_off_Ksource :
          ∀ u ∉ Ksource,
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 := by
        have hpsi0_support_Usource :
            tsupport ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex)) ⊆ Usource := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_tsupport_subset_image
                (1 : Equiv.Perm (Fin n)) phi hphiUsource
        intro u huK
        exact
          image_eq_zero_of_notMem_tsupport
            (fun hu =>
              huK (hUsource_sub_Ksource (hpsi0_support_Usource hu)))
      have hAdj_source_mem_eventually :
          ∀ᶠ eps in l, ∀ u ∈ Ksource,
            sourceSide (-1 : Real) eps eta0 u ∈
              chainAdj.terminalCarrier := by
        simpa [l, sourceSide] using
          BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (-1 : Real))
            (η := eta0) (K := Ksource) hKsource_compact
            chainAdj.terminalCarrier_open hAdj_endpoint_mem_on_Ksource
      have hterminal_to_endpoint :
          ∀ᶠ eps in l,
            (integral fun u : NPointDomain d n =>
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) eps eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)) =
            (integral fun u : NPointDomain d n =>
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) P.τ
                  (sourceSide (-1 : Real) eps eta0 u)) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)) := by
        filter_upwards [hAdj_source_mem_eventually] with eps hmem_eps
        apply integral_congr_ae
        filter_upwards with u
        by_cases huK : u ∈ Ksource
        · have hbranch :
              chainAdj.terminalBranch
                  (sourceSide (-1 : Real) eps eta0 u) =
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) P.τ
                    (sourceSide (-1 : Real) eps eta0 u)) := by
            -- Retained raw `(4.12)` provenance transported to the terminal
            -- chart.  This is the endpoint formula only after the one-branch
            -- adjacent chain has carried the raw seed forward.
            exact
              chainAdj.terminal_eq_transported_adjacent_endpoint
                (sourceSide (-1 : Real) eps eta0 u) (hmem_eps u huK)
          rw [hbranch]
        · have hzero := hpsi0_zero_off_Ksource u huK
          simp [hzero]
      have hAdj_sourceSide_fixed :
          Tendsto
            (fun eps =>
              integral fun u : NPointDomain d n =>
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) P.τ
                    (sourceSide (-1 : Real) eps eta0 u)) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u))
            l (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
        let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
        let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n
        let σAdj := P.τ.symm * (1 : Equiv.Perm (Fin n))
        let pullFlatToSource :
            SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
              ->L[Complex] SchwartzNPoint d n :=
          SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
        let psi0Flat :=
          (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm)
            ((psi0).1 : SchwartzNPoint d n)
        let BranchFlatAdj : Real -> BHW.OS45FlatCommonChartReal d n -> Complex :=
          fun eps x =>
            BHW.os45FlatCommonChartBranch d n OS lgc σAdj
              (fun j => (x j : Complex) +
                (((-eps) • eta0) j : Complex) * Complex.I)
        let FlatAdj : Real -> Complex := fun eps =>
          integral fun x : BHW.OS45FlatCommonChartReal d n =>
            BranchFlatAdj eps x *
              (SCV.translateSchwartz (-((-eps) • eta0)) psi0Flat) x
        let SourceAdj : Real -> Complex := fun eps =>
          integral fun u : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ
                (sourceSide (-1 : Real) eps eta0 u)) *
            (((psi0).1 : SchwartzNPoint d n) u)
        obtain ⟨hpsi0Flat_compact, hpsi0Flat_edge⟩ :
            HasCompactSupport
                (psi0Flat :
                  BHW.OS45FlatCommonChartReal d n -> Complex) ∧
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
        have hσAdj_symm : σAdj.symm = P.τ := by
          simp [σAdj]
        let WadjFlat :
            SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
              ->L[Complex] Complex :=
          J • (Wadj.comp pullFlatToSource)
        have hWadjFlat_def :
            WadjFlat psi0Flat =
              J * Wadj ((psi0).1 : SchwartzNPoint d n) := by
          have hpull :
              pullFlatToSource psi0Flat =
                ((psi0).1 : SchwartzNPoint d n) := by
            ext u
            simp [pullFlatToSource, psi0Flat]
          simp [WadjFlat, hpull]
        have hflatAdj_selected :
            Tendsto (fun eps => FlatAdj eps) l
              (nhds (J * Wadj ((psi0).1 : SchwartzNPoint d n))) := by
          have hflatAdj_boundary :
              Tendsto (fun eps => FlatAdj eps) l
                (nhds (WadjFlat psi0Flat)) := by
            -- Non-circular raw-adjacent flat-boundary selector.
            -- 1. Start from the retained raw `(4.12)` seed
            --    `OmegaSeed412/BSeed412`; do not replace it by the
            --    deterministic endpoint branch.
            -- 2. Transport the raw seed through `chainAdj` to the terminal
            --    flat minus chart `BHW.os45FlatCommonChartOmega d n σAdj`.
            --    Pairwise overlap equality is propagated by the checked
            --    metric-ball gallery identity theorem, with endpoint-centered
            --    restrictions at the common edge.
            -- 3. Apply the proof-local finite selector induction for
            --    `chainAdj` to
            --    `SCV.translateSchwartz (-((-eps) • eta0)) psi0Flat`, whose
            --    Schwartz limit is `psi0Flat`.
            -- 4. Rewrite the selected terminal CLM as
            --    `WadjFlat psi0Flat = J * Wadj psi0` by `hWadjFlat_def`.
            --    The downstream `extendF o permAct` formula is not used as
            --    seed data.
            have htranslateAdj :
                Tendsto
                  (fun eps : Real =>
                    SCV.translateSchwartz (-((-eps) • eta0)) psi0Flat)
                  l (nhds psi0Flat) := by
              have heps0 :
                  Tendsto (fun eps : Real => eps) l
                    (nhds (0 : Real)) := by
                simpa [l] using
                  (nhdsWithin_le_nhds :
                    nhdsWithin (0 : Real) (Set.Ioi 0) ≤
                      nhds (0 : Real))
              simpa [zero_smul] using
                (SCV.tendsto_translateSchwartz_smul_nhds_of_isCompactSupport
                  eta0 psi0Flat hpsi0Flat_compact (0 : Real)).comp heps0
            have hflatAdj_chain_transport :
                Tendsto (fun eps => FlatAdj eps) l
                  (nhds (WadjFlat psi0Flat)) := by
              -- Proof-local finite-chain boundary transport for the retained
              -- raw adjacent `(4.12)` branch.
              -- Base: the raw seed is
              -- `{z | BHW.permAct P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ`
              -- with branch `z ↦ bvt_F OS lgc n (BHW.permAct P.τ z)`;
              -- the selected fixed value is transported, not replaced by
              -- deterministic `extendF o permAct`.
              -- Step: each edge of `chainAdj` supplies a pointed overlap
              -- seed.  On the compact-support collar of the single lifted
              -- side point for
              -- `SCV.translateSchwartz (-((-eps) • eta0)) psi0Flat`, the
              -- adjacent terminal branch and the previous chart branch have
              -- equal side integrals by `integral_congr_ae`; uniqueness of
              -- limits transports the CLM across the edge.
              -- End: the terminal flat minus chart has sheet
              -- `BHW.os45FlatCommonChartOmega d n σAdj`, and the transported
              -- CLM is `WadjFlat`.  This is in-body chain induction, not a
              -- deterministic adjacent-seed shortcut.
              -- Inline the raw-adjacent `hAdj_base_selected` /
              -- `hAdj_chain_step` / `hAdj_chain_selected` block from "Flat
              -- Boundary Selector Induction" below.  The base is the retained
              -- raw `(4.12)` seed; there is no deterministic adjacent seed and
              -- no `terminal_flatBoundaryValue_translatedTest_of_chain` field.
              exact hAdj_flatBoundary_from_inline_chain
            exact hflatAdj_chain_transport
          simpa [hWadjFlat_def] using hflatAdj_boundary
        have hintegAdj_for_cancel :
            ∀ᶠ eps in l,
              Integrable
                (fun x : BHW.OS45FlatCommonChartReal d n =>
                  BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                    (fun j =>
                      ((x + ((-eps) • eta0)) j : Complex) +
                        (((-eps) • eta0) j : Complex) * Complex.I) *
                  (SCV.translateSchwartz (-((-eps) • eta0)) psi0Flat)
                    (x + ((-eps) • eta0))) := by
          filter_upwards [hpsi0Flat_integ] with eps hinteg_eps
          exact (hinteg_eps eta0 hKeta_eta0).2
        have hsource_from_flat :
            Tendsto
              (fun eps : Real =>
                integral fun u : NPointDomain d n =>
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.permAct (d := d) σAdj.symm
                      (sourceSide (-1 : Real) eps eta0 u)) *
                  psi0Flat
                    (BHW.os45CommonEdgeFlatCLE d n
                      (1 : Equiv.Perm (Fin n)) u))
              l (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
          exact
            BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest
              (d := d) (n := n) OS lgc σAdj
              (1 : Equiv.Perm (Fin n)) (-1 : Real) eta0 psi0Flat
              hintegAdj_for_cancel hflatAdj_selected
        have hsource_rewrite :
            (fun eps : Real =>
              integral fun u : NPointDomain d n =>
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) σAdj.symm
                    (sourceSide (-1 : Real) eps eta0 u)) *
                psi0Flat
                  (BHW.os45CommonEdgeFlatCLE d n
                    (1 : Equiv.Perm (Fin n)) u))
            =ᶠ[l] (fun eps : Real => SourceAdj eps) := by
          filter_upwards with eps
          apply integral_congr_ae
          filter_upwards with u
          have hpull_eval :
              psi0Flat
                  (BHW.os45CommonEdgeFlatCLE d n
                    (1 : Equiv.Perm (Fin n)) u) =
                (((psi0).1 : SchwartzNPoint d n) u) := by
            have hpull :
                pullFlatToSource psi0Flat =
                  ((psi0).1 : SchwartzNPoint d n) := by
              ext v
              simp [pullFlatToSource, psi0Flat]
            simpa [pullFlatToSource] using congrArg (fun f => f u) hpull
          simp [SourceAdj, sourceSide, hσAdj_symm, hpull_eval]
        exact hsource_from_flat.congr' hsource_rewrite
      exact hAdj_sourceSide_fixed.congr' hterminal_to_endpoint.symm

    have hAdj_moving :
        Tendsto
          (fun eps =>
            integral fun u : NPointDomain d n =>
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          l (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
      -- Use the same compact-support moving-test perturbation with the raw
      -- adjacent boundary functional `Wadj`, not with the deterministic endpoint
      -- branch as upstream data.  The fixed-test leaf gives the compact
      -- specialization `hAdj_fixed_psi0`.  The raw `(4.12)` terminal carrier plus checked
      -- SourceSide compact-collar bound gives a uniform `Msource` over one
      -- compact support containing the moving minus tests and `psi0`.  The
      -- The concrete minus-side common support and zeroth-seminorm facts are
      -- the same checked side-family lemmas, using the `sgn = -1` half of the
      -- support packet and the seminorm theorem restricted to
      -- `l = 𝓝[Set.Ioi 0] 0`.
      -- Lean update: as on the ordinary side, the moving-test support theorem
      -- is endpoint continuity, not raw-adjacent branch selection.  First prove
      -- the fixed-test selected limit from the retained raw `(4.12)` flat
      -- one-branch selector, prove the fixed-test endpoint DCT, and identify the
      -- endpoint with the selected value by `tendsto_nhds_unique`; then rewrite
      -- the already-present moving endpoint DCT.  If this chain-terminal audit
      -- expansion is used instead, the `hAdj_source_test_diff_zero`/`hsplit`
      -- block below is the checked theorem body for moving the test after
      -- `hAdj_fixed_psi0`.
      have hpsi0_zero_off_Ksource :
          ∀ u ∉ Ksource,
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 := by
        have hpsi0_support_Usource :
            tsupport ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex)) ⊆ Usource := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_tsupport_subset_image
                (1 : Equiv.Perm (Fin n)) phi hphiUsource
        intro u huK
        exact
          image_eq_zero_of_notMem_tsupport
            (fun hu =>
              huK (hUsource_sub_Ksource (hpsi0_support_Usource hu)))
      have hpsiMinus_commonCompactSupport :
          ∀ᶠ eps in l, ∀ u ∉ Ksource,
            ((((psiMinus eps eta0).1 : SchwartzNPoint d n) -
              ((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) = 0 := by
        have hpack :=
          D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually
            hUsource_open hUsource_sub_Ksource ({eta0}) isCompact_singleton
            phi hphi_compact hphiUsource
        filter_upwards [hpack] with eps hpack_eps u huK
        simpa [l, psiMinus, psi0, Pi.sub_apply] using
          (hpack_eps eta0 (by simp)).2 u huK
      have hpsiMinus_seminorm0_tendsto :
          Tendsto
            (fun eps : Real =>
              SchwartzMap.seminorm Real 0 0
                (((psiMinus eps eta0).1 : SchwartzNPoint d n) -
                  ((psi0).1 : SchwartzNPoint d n)))
            l (nhds 0) := by
        exact
          (D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero
            (1 : Equiv.Perm (Fin n)) (-1 : Real) eta0
            phi hphi_compact).mono_left nhdsWithin_le_nhds
      have hAdj_source_test_diff_zero :
          Tendsto
            (fun eps =>
              integral fun u : NPointDomain d n =>
                chainAdj.terminalBranch
                  (sourceSide (-1 : Real) eps eta0 u) *
                ((((psiMinus eps eta0).1 : SchwartzNPoint d n) -
                  ((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u))
            l (nhds 0) := by
        -- Checked neutral analytic support:
        -- `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport`
        -- with `ρperm = 1`, `sgn = -1`, `eps := fun eps => eps`,
        -- `F := chainAdj.terminalBranch`, and `K := Ksource`.
        -- Inputs are the raw-adjacent terminal carrier openness/continuity,
        -- endpoint membership on `Ksource`, and the checked minus-side
        -- support/seminorm facts above.
        exact
          BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := -1) (η := eta0)
            chainAdj.terminalCarrier_open
            chainAdj.terminalBranch_continuousOn
            hKsource_compact hAdj_endpoint_mem_on_Ksource
            (eps := fun eps : Real => eps) (by simpa [l] using tendsto_id)
            hpsiMinus_commonCompactSupport hpsiMinus_seminorm0_tendsto
      obtain ⟨MsourceAdj, _hMsourceAdj_nonneg,
          hAdj_source_bound_eventually_raw⟩ :=
        BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
          (ρperm := (1 : Equiv.Perm (Fin n)))
          (sgn := (-1 : Real)) (η := eta0)
          (K := Ksource) hKsource_compact
          chainAdj.terminalCarrier_open hAdj_endpoint_mem_on_Ksource
          chainAdj.terminalBranch_continuousOn
      have hAdj_source_bound_eventually :
          ∀ᶠ eps in l, ∀ u ∈ Ksource,
            ‖chainAdj.terminalBranch
              (sourceSide (-1 : Real) eps eta0 u)‖ ≤ MsourceAdj := by
        simpa [l, sourceSide] using hAdj_source_bound_eventually_raw
      have hAdj_source_mem_eventually :
          ∀ᶠ eps in l, ∀ u ∈ Ksource,
            sourceSide (-1 : Real) eps eta0 u ∈
              chainAdj.terminalCarrier := by
        simpa [l, sourceSide] using
          BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (-1 : Real))
            (η := eta0) (K := Ksource) hKsource_compact
            chainAdj.terminalCarrier_open hAdj_endpoint_mem_on_Ksource
      have hsplit :
          (fun eps =>
            integral fun u : NPointDomain d n =>
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          =ᶠ[l]
          (fun eps =>
            (integral fun u : NPointDomain d n =>
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) eps eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)) +
            (integral fun u : NPointDomain d n =>
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) -
                ((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))) := by
        -- Inline algebra with the same checked fixed-height integrability
        -- lemma as the ordinary side.  Inside the `filter_upwards` block, use
        -- `BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport`
        -- with `ψ = (psi0).1` and
        -- `ψ = (psiMinus eps eta0).1 - (psi0).1`, then the same
        -- `MeasureTheory.integral_add` calculation and the pointwise identity
        -- `psiMinus eps eta0 = psi0 + (psiMinus eps eta0 - psi0)`.
        -- Lean body:
        --   filter_upwards [hpsiMinus_commonCompactSupport,
        --     hAdj_source_mem_eventually, hAdj_source_bound_eventually]
        --     with eps hsupp hmem_eps hbound_eps
        --   have hfixed_int :=
        --     BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
        --       (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := -1)
        --       (eps := eps) (η := eta0)
        --       chainAdj.terminalBranch_continuousOn hKsource_compact
        --       hmem_eps hbound_eps ((psi0).1 : SchwartzNPoint d n)
        --       hpsi0_zero_off_Ksource
        --   have hdiff_int :=
        --     BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
        --       (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := -1)
        --       (eps := eps) (η := eta0)
        --       chainAdj.terminalBranch_continuousOn hKsource_compact
        --       hmem_eps hbound_eps
        --       (((psiMinus eps eta0).1 : SchwartzNPoint d n) -
        --         ((psi0).1 : SchwartzNPoint d n))
        --       (fun u huK => hsupp u huK)
        --   rw [← MeasureTheory.integral_add hfixed_int hdiff_int]
        --   apply integral_congr_ae
        --   filter_upwards with u
        --   simp [Pi.sub_apply, sub_eq_add_neg, mul_add, add_comm,
        --     add_left_comm, add_assoc]
      exact (hAdj_fixed_psi0.add hAdj_source_test_diff_zero).congr' hsplit.symm

    have hAdj_boundary_to_source :
        Wadj ((psi0).1 : SchwartzNPoint d n) =
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u) := by
      have hAdj_endpoint_limit :
          Tendsto
            (fun eps =>
              integral fun u : NPointDomain d n =>
                chainAdj.terminalBranch
                  (sourceSide (-1 : Real) eps eta0 u) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u))
            l
            (nhds
              (∫ u : NPointDomain d n,
                chainAdj.terminalBranch
                  (sourceSide (-1 : Real) 0 eta0 u) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u))) := by
        have hpsi0_compact :
            HasCompactSupport
              (((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_hasCompactSupport
                (1 : Equiv.Perm (Fin n)) phi
        have hpsi0_support_V :
            tsupport
              (((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) ⊆ P.V := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_tsupport_subset_V
                (1 : Equiv.Perm (Fin n)) phi hphiE
        have hAdj_endpoint_mem :
            ∀ u ∈ tsupport
                (((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex),
              sourceSide (-1 : Real) 0 eta0 u ∈
                chainAdj.terminalCarrier := by
          intro u hu
          have huV : u ∈ P.V := hpsi0_support_V hu
          have hzero :
              sourceSide (-1 : Real) 0 eta0 u =
                BHW.os45QuarterTurnConfig
                  (fun k => wickRotatePoint (u k)) := by
            simpa [sourceSide]
              using
                BHW.os45FlatCommonChartSourceSide_zero
                  (d := d) (n := n)
                  (ρperm := (1 : Equiv.Perm (Fin n)))
                  (sgn := (-1 : Real)) (η := eta0) (u := u)
          have hwindow :
              BHW.os45QuarterTurnConfig
                  (fun k => wickRotatePoint (u k)) ∈
                chainAdj.terminalCarrier := by
            -- This is the retained raw `(4.12)` terminal common-edge window,
            -- built from `H.adjacentCommonEdge_metricBallChartInWindow` after
            -- raw-chain transport.  It is not the downstream deterministic
            -- adjacent branch.
            exact chainAdj.terminal_contains_adjacentCommonEdge u huV
          simpa [hzero] using hwindow
        have hAdj_eventual_collar :
            ∀ᶠ eps in l,
              ∀ u ∈ tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex),
                sourceSide (-1 : Real) eps eta0 u ∈
                  chainAdj.terminalCarrier := by
          exact
            BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
              (ρperm := (1 : Equiv.Perm (Fin n)))
              (sgn := (-1 : Real)) (η := eta0)
              (K :=
                tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex))
              hpsi0_compact.isCompact
              chainAdj.terminalCarrier_open
              hAdj_endpoint_mem
        have hAdj_pointwise :
            ∀ u : NPointDomain d n,
              Tendsto
                (fun eps =>
                  chainAdj.terminalBranch
                    (sourceSide (-1 : Real) eps eta0 u) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u))
                l
                (nhds
                  (chainAdj.terminalBranch
                    (sourceSide (-1 : Real) 0 eta0 u) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u))) := by
          intro u
          by_cases hu :
              u ∈ tsupport
                (((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex)
          · have hbranch_tendsto :
                Tendsto
                  (fun eps : Real =>
                    chainAdj.terminalBranch
                      (sourceSide (-1 : Real) eps eta0 u))
                  l
                  (nhds
                    (chainAdj.terminalBranch
                      (sourceSide (-1 : Real) 0 eta0 u))) := by
              exact
                BHW.tendsto_comp_os45FlatCommonChartSourceSide_nhdsWithin
                  (d := d) (n := n)
                  (ρperm := (1 : Equiv.Perm (Fin n)))
                  (sgn := (-1 : Real)) (η := eta0) (u := u)
                  chainAdj.terminalCarrier_open
                  chainAdj.terminalBranch_continuousOn
                  (hAdj_endpoint_mem u hu)
            exact hbranch_tendsto.mul tendsto_const_nhds
          · have hzero :
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) = 0 :=
              image_eq_zero_of_notMem_tsupport hu
            simpa [hzero]
        have hAdj_bound :
            ∃ g : NPointDomain d n -> Real,
              Integrable g ∧
              ∀ᶠ eps in l,
                ∀ᵐ u : NPointDomain d n,
                  ‖chainAdj.terminalBranch
                    (sourceSide (-1 : Real) eps eta0 u) *
                    ((((psi0).1 : SchwartzNPoint d n) :
                      NPointDomain d n -> Complex) u)‖ ≤ g u := by
          rcases
            BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
              (ρperm := (1 : Equiv.Perm (Fin n)))
              (sgn := (-1 : Real)) (η := eta0)
              (K :=
                tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex))
              hpsi0_compact.isCompact
              chainAdj.terminalCarrier_open
              hAdj_endpoint_mem
              chainAdj.terminalBranch_continuousOn with
            ⟨MAdj, hMAdj_nonneg, hMAdj_bound⟩
          refine ⟨
            fun u : NPointDomain d n =>
              MAdj *
                ‖((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u)‖,
            ?_, ?_⟩
          · have hpsi0_integrable :
                Integrable
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex)) := by
              simpa using
                (SchwartzMap.integrable
                  ((psi0).1 : SchwartzNPoint d n))
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (hpsi0_integrable.norm.const_mul MAdj)
          · filter_upwards [hMAdj_bound] with eps hMadj
            filter_upwards with u
            by_cases hu :
                u ∈ tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex)
            · calc
                ‖chainAdj.terminalBranch
                    (sourceSide (-1 : Real) eps eta0 u) *
                    ((((psi0).1 : SchwartzNPoint d n) :
                      NPointDomain d n -> Complex) u)‖
                    = ‖chainAdj.terminalBranch
                        (sourceSide (-1 : Real) eps eta0 u)‖ *
                      ‖((((psi0).1 : SchwartzNPoint d n) :
                        NPointDomain d n -> Complex) u)‖ := by
                        simp [norm_mul]
                _ ≤ MAdj *
                      ‖((((psi0).1 : SchwartzNPoint d n) :
                        NPointDomain d n -> Complex) u)‖ :=
                    mul_le_mul_of_nonneg_right (hMadj u hu) (norm_nonneg _)
            · have hzero :
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u) = 0 :=
                image_eq_zero_of_notMem_tsupport hu
              simp [hzero, hMAdj_nonneg]
        rcases hAdj_bound with ⟨g, hg_int, hg_bound⟩
        have hAdj_aestrongly :
            ∀ᶠ eps in l,
              AEStronglyMeasurable
                (fun u : NPointDomain d n =>
                  chainAdj.terminalBranch
                    (sourceSide (-1 : Real) eps eta0 u) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u)) := by
          filter_upwards [hAdj_eventual_collar] with eps heps
          let K : Set (NPointDomain d n) :=
            tsupport
              (((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex)
          let f : NPointDomain d n -> Complex := fun u =>
            chainAdj.terminalBranch
              (sourceSide (-1 : Real) eps eta0 u) *
            ((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u)
          have hK_compact : IsCompact K := hpsi0_compact.isCompact
          have hsource_cont :
              Continuous fun u : NPointDomain d n =>
                sourceSide (-1 : Real) eps eta0 u := by
            simpa [sourceSide]
              using
                BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
                  (d := d) (n := n)
                  (ρperm := (1 : Equiv.Perm (Fin n)))
                  (sgn := (-1 : Real)) (eps := eps) (η := eta0)
          have hbranch_cont_on_K :
              ContinuousOn
                (fun u : NPointDomain d n =>
                  chainAdj.terminalBranch
                    (sourceSide (-1 : Real) eps eta0 u)) K := by
            exact
              chainAdj.terminalBranch_continuousOn.comp
                hsource_cont.continuousOn heps
          have htest_cont :
              Continuous
                (((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) :=
            ((psi0).1 : SchwartzNPoint d n).continuous
          have hzero_off :
              ∀ u ∉ K, f u = 0 := by
            intro u hu
            have hzero :
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) = 0 :=
              image_eq_zero_of_notMem_tsupport hu
            simp [f, hzero]
          exact
            BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport
              (K := K) hK_compact
              hbranch_cont_on_K htest_cont.continuousOn hzero_off
        apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (bound := g)
        · exact hAdj_aestrongly
        · exact hg_bound
        · exact hg_int
        · intro u
          exact hAdj_pointwise u
      have hAdj_endpoint_as_source :
          (∫ u : NPointDomain d n,
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) 0 eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)) =
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
        have hpsi0_support_V :
            tsupport
              (((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) ⊆ P.V := by
          simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
            using
              D.toSchwartzNPointCLM_tsupport_subset_V
                (1 : Equiv.Perm (Fin n)) phi hphiE
        have hAdj_endpoint_as_carrier :
            (∫ u : NPointDomain d n,
                chainAdj.terminalBranch
                    (sourceSide (-1 : Real) 0 eta0 u) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u)) =
              ∫ u : NPointDomain d n,
                bvt_F OS lgc n
                    (BHW.os45QuarterTurnConfig
                      (fun k => wickRotatePoint (u (P.τ k)))) *
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u) := by
          have hAdj_endpoint_pointwise :
            ∀ᵐ u : NPointDomain d n,
              chainAdj.terminalBranch
                  (sourceSide (-1 : Real) 0 eta0 u) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) =
              bvt_F OS lgc n
                  (BHW.os45QuarterTurnConfig
                    (fun k => wickRotatePoint (u (P.τ k)))) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) := by
            filter_upwards with u
            by_cases hu :
                u ∈ tsupport
                  (((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex)
            · have huV : u ∈ P.V := hpsi0_support_V hu
              have hsource_zero :
                  sourceSide (-1 : Real) 0 eta0 u =
                    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                      (BHW.realEmbed
                        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) u)) := by
                simpa [sourceSide] using
                  BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
                    (d := d) (n := n)
                    (ρperm := (1 : Equiv.Perm (Fin n)))
                    (sgn := (-1 : Real)) (η := eta0) (u := u)
              have hbranch :
                  chainAdj.terminalBranch
                      (sourceSide (-1 : Real) 0 eta0 u) =
                    bvt_F OS lgc n
                      (BHW.permAct (d := d) P.τ
                        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                          (BHW.realEmbed
                            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                              (1 : Equiv.Perm (Fin n)) u)))) := by
                -- Use the retained raw `(4.12)` branch formula transported
                -- through `chainAdj` to the terminal endpoint.  The raw seed is
                -- `{z | BHW.permAct P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ`
                -- with branch `z ↦ bvt_F OS lgc n (BHW.permAct P.τ z)`.
                -- This is not the downstream deterministic initial datum.
                simpa [hsource_zero] using
                  chainAdj.terminal_eq_raw412_seed
                    (sourceSide (-1 : Real) 0 eta0 u)
              have hperm_quarter :
                  BHW.permAct (d := d) P.τ
                      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                        (BHW.realEmbed
                          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                            (1 : Equiv.Perm (Fin n)) u))) =
                    BHW.os45QuarterTurnConfig
                      (fun k => wickRotatePoint (u (P.τ k))) := by
                -- Carrier identity only.  The inverse quarter-turn of the real
                -- common edge is the positive quarter-turned Wick carrier, and
                -- `permAct` just reindexes that carrier.  This deliberately
                -- does not claim equality with the unturned Wick point.
                simpa using
                  BHW.permAct_os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick
                    (d := d) (n := n)
                    (τ := P.τ) (ρperm := (1 : Equiv.Perm (Fin n))) (u := u)
              rw [hbranch, hperm_quarter]
            · have hzero :
                  ((((psi0).1 : SchwartzNPoint d n) :
                    NPointDomain d n -> Complex) u) = 0 :=
                image_eq_zero_of_notMem_tsupport hu
              simp [hzero]
          exact integral_congr_ae hAdj_endpoint_pointwise
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
                    NPointDomain d n -> Complex) u) := by
          let e := BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n))
          let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n
          let psi0Flat :=
            (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm)
              ((psi0).1 : SchwartzNPoint d n)
          let pullFlatToSource :
              SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
                ->L[Complex] SchwartzNPoint d n :=
            SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
          let carrierAdjPairing : Complex :=
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n
                  (BHW.os45QuarterTurnConfig
                    (fun k => wickRotatePoint (u (P.τ k)))) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u)
          let wickAdjPairing : Complex :=
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n
                (fun k => wickRotatePoint (u (P.τ k))) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u)
          let WadjFlat :
              SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
                ->L[Complex] Complex :=
            J • (Wadj.comp pullFlatToSource)
          have hJ_ne : J ≠ 0 := by
            exact
              Complex.ofReal_ne_zero.mpr
                (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
          have hWadj_carrier :
              WadjFlat psi0Flat = J * carrierAdjPairing := by
            -- Proof-local transcript:
            -- 1. `pullFlatToSource psi0Flat = psi0` by the CLE inverse
            --    calculation, then `simp [WadjFlat]` reduces the left side to
            --    `J * Wadj psi0`.
            -- 2. `hWadj_endpoint` identifies `Wadj psi0` with the zero-height
            --    adjacent source-side endpoint integral.
            -- 3. `hAdj_endpoint_as_carrier` rewrites that endpoint integral to
            --    `carrierAdjPairing`, using
            --    `BHW.permAct_os45FlatCommonChartSourceSide_zero`,
            --    `chainAdj.terminal_eq_raw412_seed`, and the raw `(4.12)`
            --    seed formula.  This is the only place raw adjacent terminal
            --    provenance is used here.
            calc
              WadjFlat psi0Flat = J * Wadj ((psi0).1 : SchwartzNPoint d n) := by
                have hpull :
                    pullFlatToSource psi0Flat =
                      ((psi0).1 : SchwartzNPoint d n) := by
                  ext u
                  simp [pullFlatToSource, psi0Flat]
                simp [WadjFlat, hpull]
              _ = J * carrierAdjPairing := by
                rw [hWadj_endpoint, hAdj_endpoint_as_carrier]
          have hWadj_wick :
              WadjFlat psi0Flat = J * wickAdjPairing := by
            -- Proof-local transcript:
            -- 1. reduce to `J * Wadj psi0`;
            -- 2. use the raw `(4.12)` Wick trace transported by `chainAdj` to
            --    get `Wadj psi0 = wickAdjPairing`;
            -- 3. the checked source normalization
            --    `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger`
            --    can be used to identify this same pairing with the Schwinger
            --    value when needed.  No deterministic adjacent seed, `Hdiff`,
            --    or common-boundary CLM is in scope.
            have hWadj_adjWick :
                Wadj ((psi0).1 : SchwartzNPoint d n) = wickAdjPairing := by
              -- Raw `(4.12)` Wick trace, transported along `chainAdj`.
              exact hAdj_currentTest_adjacentWick
            calc
              WadjFlat psi0Flat = J * Wadj ((psi0).1 : SchwartzNPoint d n) := by
                have hpull :
                    pullFlatToSource psi0Flat =
                      ((psi0).1 : SchwartzNPoint d n) := by
                  ext u
                  simp [pullFlatToSource, psi0Flat]
                simp [WadjFlat, hpull]
              _ = J * wickAdjPairing := by
                rw [hWadj_adjWick]
          have hmul : J * carrierAdjPairing = J * wickAdjPairing :=
            hWadj_carrier.symm.trans hWadj_wick
          exact mul_left_cancel₀ hJ_ne hmul
        exact hAdj_endpoint_as_carrier.trans hAdj_carrier_pairing
      have hWadj_endpoint :
          Wadj ((psi0).1 : SchwartzNPoint d n) =
            ∫ u : NPointDomain d n,
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) 0 eta0 u) *
              ((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u) := by
        exact tendsto_nhds_unique hAdj_fixed_psi0 hAdj_endpoint_limit
      exact hWadj_endpoint.trans hAdj_endpoint_as_source

    have hAdj_source_norm :
        Wadj ((psi0).1 : SchwartzNPoint d n) =
          OS.S n (D.toZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) phi) := by
      calc
        Wadj ((psi0).1 : SchwartzNPoint d n)
            = ∫ u : NPointDomain d n,
                bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
                ((((psi0).1 : SchwartzNPoint d n) :
                  NPointDomain d n -> Complex) u) :=
              hAdj_boundary_to_source
        _ = OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi) := by
              -- Convert `psi0` to `D.toSchwartzNPointCLM 1 phi` and use the
              -- checked adjacent source normalizer.  This is the E3/source
              -- covariance step after raw `(4.12)` terminal transport, not a
              -- branch-selection statement.
              simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
                using
                BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger
                  (d := d) OS lgc D phi hphiE

    have hAdj_as_terminal :
        Tendsto
          (fun eps =>
            integral fun u : NPointDomain d n =>
              Badj_terminal (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          l
          (nhds
            (OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
      exact hAdj_moving.congr' hAdj_integral_rewrite.symm |>.congr
        (by simpa [hAdj_source_norm])

    exact hAdj_as_terminal.const_mul Jflat

  have hSourceMinus_eta0 :
      Tendsto (fun eps => SourceMinusSide eps eta0) l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    exact (hSourceMinus_common.tendsto hKeta_eta0)

  have hbranch :
      Tendsto (fun eps => BranchMinusSide eps eta0) l
        (nhds
          (Jflat *
            OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) phi))) := by
    exact hBranchMinus_to_common.congr' hminus_pullback.symm

  exact hbranch.sub hSourceMinus_eta0 |>.congr'
    (by filter_upwards with eps; ring_nf)

have hMinus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      l Keta := by
  simpa [Keta] using
    (SCV.tendstoUniformlyOn_singleton_iff_tendsto
      (F := fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
      (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (p := l) (x := eta0)).2 hMinus_asymptotic_eta0
```

Once those two transfers are proved, the rest is checked filter algebra:

```lean
have hBranchPlus_common :
    TendstoUniformlyOn BranchPlusSide
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        Jflat * OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))
      l Keta :=
  SCV.tendstoUniformlyOn_of_sub_tendstoUniformlyOn_zero
    hPlus_asymptotic hSourcePlus_common

have hBranchMinus_common :
    TendstoUniformlyOn BranchMinusSide
      (fun _ : BHW.OS45FlatCommonChartReal d n =>
        Jflat * OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi))
      l Keta :=
  SCV.tendstoUniformlyOn_of_sub_tendstoUniformlyOn_zero
    hMinus_asymptotic hSourceMinus_common

have hEdge_eq : AdjEdge = OrdEdge := by
  exact
    (SCV.eq_zeroHeight_of_common_sideLimit
      hKeta_nonempty
      hBranchMinus_zero hBranchPlus_zero
      hBranchMinus_common hBranchPlus_common)

have hflat_zero :
    integral fun x : BHW.OS45FlatCommonChartReal d n =>
      (BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : Complex)) -
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n)) (fun a => (x a : Complex))) * phi x
      = 0 := by
  -- Expand `AdjEdge`, `OrdEdge`; use integrability from compact support and
  -- continuity on the real edge, then rewrite by `hEdge_eq`.
  -- This is the standard `integral_sub`/ring rewrite and should be inlined.
```

This block no longer introduces a public transfer theorem.  The ordinary and
adjacent transfer bodies are the genuine mathematical work; the final
`hflat_zero` step is only the standard `integral_sub`/ring rewrite from
`AdjEdge = OrdEdge`.

#### Code-Level Obstruction Audit

The current Lean code already proves many facts that make a shortcut look
available, but they do not discharge the strict OS-I leaf.

Checked and usable:

* `BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24` gives a uniform
  side-height window for compact flat support and compact cone directions.
* `D.toSideZeroDiagonalCLM_apply`,
  `D.toSideZeroDiagonalCLM_tsupport_subset_image_eventually`, and
  `D.toSideZeroDiagonalCLM_tendsto_zero` give the exact source-test formula,
  eventual source-window support, and ambient Schwartz convergence.
* `D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger` gives the
  checked source-side Schwinger normalization/support package for the signed
  cutoff families.  It is consumed at the endpoint/moving-test stage; it is
  not the finite chart-transport selector.
* `SCV.tube_boundaryValueData_moving_of_fixed` and
  `bvt_boundary_values_moving` upgrade fixed-test boundary values to moving
  tests after a boundary CLM has already been selected.
* `BHW.os45FlatCommonChart_ordinaryEdgeCLM_apply` identifies the plus
  zero-height pairing with `Tlocal`, and
  `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`
  consumes the directly proved `hzero_plus`/`hzero_minus` pairings to produce
  the flat EOW seed.  The older source-representation reducer is a retired
  downstream convenience, not the upstream crossing route.

Tempting but not allowed as the upstream adjacent proof:

```lean
let Fdet : (Fin n -> Fin (d + 1) -> Complex) -> Complex := fun z =>
  BHW.extendF (bvt_F OS lgc n)
    (BHW.permAct (d := d) P.τ z)
```

The code has deterministic holomorphy and endpoint bookkeeping for `Fdet`.
It also agrees with the raw `(4.12)` seed on the literal preimage-forward-tube
seed window after rewriting by `extendF_eq_on_forwardTube`.  Those facts are
downstream bookkeeping only in this Stage-A proof.  Promoting `Fdet` to the
upstream adjacent analytic element before the raw `(4.12)` seed has been
transported through the Figure-2-4 circuit erases the selected OS-I analytic
element whose boundary comparison is being proved.  In particular, a proof
that starts the adjacent chain from `Fdet` on the initial-sector overlap has
not proved the adjacent branch/source asymptotic transfer; it has assumed the
endpoint boundary comparison that the strict route must derive.

Lean implementation leaves to establish in-body from the transcript, not to
expose as public theorem surfaces:

* the ordinary `(4.1)` branch/source asymptotic transfer, with the ordinary
  endpoint chain and source/flat side-family identification unfolded.
* the raw-adjacent `(4.12)` branch/source asymptotic transfer, with the raw
  `OmegaSeed412/BSeed412` provenance retained until the terminal endpoint.
* the adjacent analytic-element uniqueness seed in the finite gallery, unless
  it is replaced by an explicit proof that does not use `Fdet` as upstream
  data.

These three bullets are the inline implementation body for the upstream
`hadj412` flat real-Jost crossing.  After these local haves are established,
the proof immediately calls the already checked local zero-height flat EOW
bridge.  A public horizontal pairing zero theorem before that in-body proof
would still be premature.  Any production lemma that assumes the
flat zero, assumes either asymptotic transfer, assumes `Hdiff`, assumes `Wadj`,
or assumes a common-boundary CLM is still wrapper churn.

#### Direct One-Branch Producer Gate

Implementation audit, 2026-05-17: the names `chainOrd`, `chainAdj`, `Word`,
`Wadj`, `hOrd_fixed_psi0`, `hAdj_fixed_psi0`, and the terminal trace fields
below are currently transcript locals.  They may be introduced in Lean only as
objects produced by the direct OS-I one-branch construction, not as fields of a
new assumption packet.

The direct producer must start by constructing two private one-branch chains
from concrete incoming analytic elements:

```lean
-- Ordinary `(4.1)` incoming element.
let OmegaOrd0 : Set (Fin n -> Fin (d + 1) -> Complex) :=
  BHW.ExtendedTube d n ∩ H.ΩJ
let BOrd0 : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => BHW.extendF (bvt_F OS lgc n) z

-- Raw adjacent `(4.12)` incoming element.
let OmegaSeed412 : Set (Fin n -> Fin (d + 1) -> Complex) :=
  {z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ
let BSeed412 : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
```

The ordinary chain is allowed to compare charts to the common model `BOrd0` on
`OmegaOrd0`.  The adjacent chain is allowed to compare charts to `BSeed412` on
`OmegaSeed412` only.  It may rewrite the terminal chart to the deterministic
endpoint model

```lean
fun z => BHW.extendF (bvt_F OS lgc n)
  (BHW.permAct (d := d) P.τ z)
```

only after the retained raw `(4.12)` chain has reached that terminal chart and
the endpoint equality has been proved.  This distinction is load-bearing:
using the deterministic endpoint branch as the adjacent incoming seed assumes
the OS-I transfer that this block is meant to prove.

There are two different chain regimes, and the implementation must not blur
them.

For the upstream fixed-test source-current selector, construct two independent
one-branch corridors:

* Ordinary source selector.  Every chart in `chainOrd` is a restriction of the
  ordinary analytic element `BOrd0 = BHW.extendF (bvt_F OS lgc n)`.  Each edge is
  produced by comparing both chart branches to `BOrd0` on a common metric
  subball, then using the checked pointed common-model edge consumer.  The
  terminal chart is the flat plus chart, still with model `BOrd0`.
* Raw-adjacent source selector.  Every chart in `chainAdj` is retained raw
  `(4.12)` provenance.  Interior raw charts compare to
  `OmegaSeed412/BSeed412` along
  `gammaAdjSeed t = BHW.permAct P.τ (gammaOrd t)`; the terminal flat-minus
  chart may be rewritten to the
  deterministic endpoint model `extendF o permAct P.τ` only after the raw
  terminal edge has been constructed from the same retained seed and the
  positive-height support has been shown to lie where
  `permAct P.τ z ∈ BHW.ForwardTube d n`.  That terminal rewrite uses
  `BHW.extendF_eq_on_forwardTube` as local bookkeeping; it is not the incoming
  seed.

For downstream all-overlap identity propagation, after the source selector has
already produced `hzero_plus` and `hzero_minus`, the flat plus/minus EOW edge is
available by
`flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM`.  That edge is
not in scope while proving the source-current selector itself.  In particular,
the selector chain must not be built through the `LocalOverlapAtZ0.flat_*`
constructors or any data structure carrying the current `hzero_minus`.

The output needed by the side-height block is proof-local and current-test
specialized.  It is not a list of assumptions; each item is constructed by the
exact side-height transfer block below.

| local name | proof source inside the block |
| --- | --- |
| `hOrd_fixed_psi0` | ordinary fixed-test source-side quarter-turn script: finite-chain flat boundary transport selects `WordFlat psi0Flat`, the checked scalar-cancellation theorem converts this to the source-side limit landing in `Word psi0`, then `chainOrd.terminal_eq_ordinary_global` rewrites from `extendF` to `chainOrd.terminalBranch`. |
| `hOrd_endpoint_limit` | checked source-side endpoint DCT for `chainOrd.terminalBranch` on the compact collar, using `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport`. |
| `hOrd_currentTest_schwinger` / `hOrd_boundary_to_source` | uniqueness of `hOrd_fixed_psi0` and `hOrd_endpoint_limit`, followed by ordinary endpoint trace normalization and `bvt_euclidean_restriction` for `D.toZeroDiagonalCLM 1 phi`. |
| `hAdj_fixed_psi0` | adjacent fixed-test source-side quarter-turn script: finite-chain flat boundary transport from the retained raw `(4.12)` seed selects `WadjFlat psi0Flat`, the checked scalar-cancellation theorem converts this to the source-side limit landing in `Wadj psi0`, then terminal transport rewrites from endpoint `extendF o permAct` to `chainAdj.terminalBranch`. |
| `hAdj_endpoint_limit` | checked source-side endpoint DCT for `chainAdj.terminalBranch` on the compact collar. |
| `hAdj_currentTest_adjacentWick` / `hAdj_boundary_to_source` | uniqueness of `hAdj_fixed_psi0` and `hAdj_endpoint_limit`, retained raw `(4.12)` Wick trace at the endpoint, and `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger` only after raw transport. |

The fixed-test `Tendsto` statements come from the current one-branch analytic
element and its retained OS-I boundary datum.  The endpoint `Tendsto` statements
come from the checked source-side DCT theorem.  The current-test statements are
uniqueness-of-limits plus endpoint trace normalization.  None of these may be
made into a public theorem that assumes the chain, `Word`, or `Wadj`; if a
helper is split out, it must construct the finite chain or prove a neutral
topological/analytic fact used immediately by this block.

#### Flat Boundary Selector Induction

The older local script names
`chainOrd.terminal_flatBoundaryValue_translatedTest_of_chain` and
`chainAdj.terminal_flatBoundaryValue_translatedTest_of_chain` are retired.
In Lean these points must be expanded as finite inductions over the already
constructed one-branch chain.

For the ordinary chain, the local induction has this shape.  The term
`sideLift` is the common lifted side point defined in the single-edge block
below.  The induction transports one concrete limit value all the way to the
terminal chart; it does not store or assume a family of `boundaryCLM` fields.

Important implementation correction: the displayed `sideLift` specialization
below is the terminal flat/source-side approach.  It is not automatically the
initial OS-I `(4.1)` or raw `(4.12)` approach.  In Lean the finite induction
must therefore carry a proof-local approach family for each chart,

```lean
chartApproach :
  (j : Fin (chain.len + 1)) ->
    Real -> BHW.OS45FlatCommonChartReal d n ->
      (Fin n -> Fin (d + 1) -> Complex)

testFamily :
  (j : Fin (chain.len + 1)) ->
    Real -> SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
```

with these exact endpoint contracts:

* `chartApproach 0` is the genuine incoming OS-I ray after the checked CLE/test
  pullback needed to put the base integral in flat variables; its limit is
  supplied by `ordinary41_fixed_test_boundaryValue_extendF` or
  `raw412_fixed_test_boundaryValue`.
* `chartApproach (Fin.last chain.len)` is the terminal `sideLift` above and
  `testFamily (Fin.last chain.len) eps` is the translated flat test used by
  `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest`.
* every successor step proves eventual integral equality between the two
  adjacent chart-local approach families on the compact support, after
  promoting the stored seed to carrier-intersection equality by
  `PointedMetricBranchChart.eqOn_inter_of_seed`.

Thus the base is a genuine OS-I boundary-value theorem, not a sourceSide limit
assumed at chart `0`.  If the implementation instead evaluates every chart at
the terminal `sideLift`, then `hOrd_base_selected`/`hAdj_base_selected` becomes
circular and must be rejected.

Lean-facing current-test specialization:

```lean
let Lcur : Complex :=
  OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi)

-- For each branch kind, use the path chosen in the finite-chain assembly:
--   ordinary: gammaOrd
--   raw adjacent source-current: gammaAdjSeed
-- The chain stores charts and pointed seed edges; the approach data below is
-- local notation inside the proof, not a public structure.

let chartApproach
    (kind : BranchKind) (j : Fin (chain kind).len.succ)
    (eps : Real) (x : BHW.OS45FlatCommonChartReal d n) :
    Fin n -> Fin (d + 1) -> Complex := by
  -- chart-local positive-side family based at `gammaOf kind t_j`.
  -- At `j = 0`, ordinary is the Wick-anchor/current Schwinger family;
  -- adjacent is the raw `(4.12)` seed family based at `gammaAdjSeed 0`.
  -- At `j = last`, this is the terminal flat side family that rewrites to
  -- `BHW.os45FlatCommonChartBranch ...`.

let chartTest
    (kind : BranchKind) (j : Fin (chain kind).len.succ)
    (eps : Real) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex := by
  -- same compact test transported through the local chart/CLE bookkeeping.
  -- Terminal ordinary is `SCV.translateSchwartz (-(eps • eta0)) psi0Flat`;
  -- terminal adjacent is
  -- `SCV.translateSchwartz (-((-eps) • eta0)) psi0Flat`.

let I (kind : BranchKind) (j : Fin (chain kind).len.succ) (eps : Real) :=
  ∫ x : BHW.OS45FlatCommonChartReal d n,
    ((chain kind).chart j).branch (chartApproach kind j eps x) *
      chartTest kind j eps x

have hbase_current :
    Tendsto (fun eps => I kind 0 eps) l (nhds (J * Lcur)) := by
  cases kind
  · -- ordinary base: rewrite chart `0` to the Wick-anchor current pairing.
    -- Use the support-local `extendF = bvt_F` on the ordinary Wick/forward
    -- tube, then `bvt_euclidean_restriction` for
    -- `D.toZeroDiagonalCLM 1 phi`.
  · -- raw adjacent base: chart `0` is at
    -- `gammaAdjSeed 0 = BHW.permAct P.τ (gammaOrd 0)` with branch
    -- `BSeed412`.  Rewrite the current compact pairing to
    -- `bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k)))`, then use
    -- `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger`.
    -- Do not evaluate `BSeed412` at `gammaOrd 0`.

have hstep_current :
    ∀ j : Fin (chain kind).len,
      ∀ᶠ eps in l,
        I kind (Fin.castSucc j) eps = I kind (Fin.succ j) eps := by
  intro j
  -- First promote the stored pointed seed to equality on the full carrier
  -- intersection by `PointedMetricBranchChart.eqOn_inter_of_seed`.
  -- Then prove the chart-local approach family for this edge eventually lies
  -- in that intersection on the compact transported support.  Any coordinate
  -- change between `chartApproach kind (Fin.castSucc j)` and
  -- `chartApproach kind (Fin.succ j)` must be discharged here by the checked
  -- CLE/test pullback for this local chart.  There is no terminal `sideLift`
  -- shortcut at intermediate charts.

have hchain_current :
    ∀ (j : Nat) (hj : j ≤ (chain kind).len),
      Tendsto
        (fun eps => I kind ⟨j, Nat.lt_succ_of_le hj⟩ eps)
        l (nhds (J * Lcur)) := by
  -- finite `Nat` induction from `hbase_current`; successor uses
  -- `(hstep_current ⟨j, hj⟩).symm` and `Tendsto.congr'`.

have hflatOrd_boundary_current :
    Tendsto (fun eps => FlatOrd eps) l (nhds (J * Lcur)) := by
  -- instantiate `hchain_current` with `kind = ordinary41` at the last chart;
  -- terminal rewrite only here uses the ordinary flat plus branch
  -- `BHW.os45FlatCommonChartBranch d n OS lgc 1`.

have hflatAdj_boundary_current :
    Tendsto (fun eps => FlatAdj eps) l (nhds (J * Lcur)) := by
  -- instantiate `hchain_current` with `kind = adjacent412Source` at the last
  -- chart; terminal rewrite only here uses the raw adjacent terminal flat
  -- branch with `σAdj = P.τ.symm * 1`.  Any `extendF o permAct` expression is
      -- support-local terminal normal form, not seed data.
```

The focused current implementation transcript has been split to
`docs/theorem2_source_current_selector_transcript.md`.  Use it for the exact
two-hole recipe in the current Hdiff body.  The section here remains the
mathematical explanation of why the selector must be a one-branch,
chart-local induction rather than a terminal `sideLift` shortcut.

##### Single Edge Integral Equality

The successor step in both finite inductions must be implemented at the level
of one adjacent pair of metric-ball charts.  A raw `PointedSeedEdge.eqOn`
compares the branches only on its seed neighborhood; that neighborhood is not
large enough for the moving side collar.  The proof must first promote the seed
with `PointedMetricBranchChart.eqOn_inter_of_seed`, obtaining equality on the
full intersection of the two metric-ball carriers.  Only then does compactness
of the translated support show that the single lifted side argument lies in
both carriers.

For a signed branch label `sgn` and a chain edge
`edge : PointedSeedEdge zBase Nprev Nnext Fprev Fnext`, define the common
side lift in the proof body:

```lean
let flatSide (sgn eps : Real)
    (eta x : BHW.OS45FlatCommonChartReal d n) :
    BHW.OS45FlatCommonChartSpace d n :=
  fun a => (x a : Complex) + (((sgn * eps) • eta) a : Complex) * Complex.I

let sideLift (sgn eps : Real)
    (eta x : BHW.OS45FlatCommonChartReal d n) :
    Fin n -> Fin (d + 1) -> Complex :=
  (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
    (BHW.unflattenCfg n d (flatSide sgn eps eta x))
```

For the ordinary selector use `sgn = 1`; for the raw-adjacent selector use
`sgn = -1` with the same flat vector `eta0`.  The edge step then has the same
shape on both sides:

```lean
have hedge_integral_eq
    (j : Nat) (hj : j < chain.len)
    (A := chain.chart ⟨j, Nat.lt_succ_of_lt hj⟩)
    (B := chain.chart ⟨j + 1, Nat.succ_lt_succ hj⟩)
    (edge := chain.edge j hj)
    (hψeps_def :
      ∀ eps,
        ψeps eps =
          SCV.translateSchwartz (-(sgn * eps) • eta0) psi0Flat) :
    ∀ᶠ eps in l,
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        chain.branch j (sideLift sgn eps eta0 x) *
          ψeps eps x =
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        chain.branch (j + 1) (sideLift sgn eps eta0 x) *
          ψeps eps x := by
  have hEq_inter :
      Set.EqOn A.branch B.branch (A.carrier ∩ B.carrier) :=
    PointedMetricBranchChart.eqOn_inter_of_seed A B
      ⟨edge.W, edge.W_open, edge.z0_mem, edge.W_sub, edge.eqOn⟩

  have hA_zero :
      ∀ y ∈ tsupport (psi0Flat :
          BHW.OS45FlatCommonChartReal d n -> Complex),
        sideLift sgn 0 eta0 y ∈ A.carrier := by
    intro y hy
    exact chain.chart_zero_tsupport_mem j hj y hy |>.1

  have hB_zero :
      ∀ y ∈ tsupport (psi0Flat :
          BHW.OS45FlatCommonChartReal d n -> Complex),
        sideLift sgn 0 eta0 y ∈ B.carrier := by
    intro y hy
    exact chain.chart_zero_tsupport_mem j hj y hy |>.2

  have hedge_collar :
      ∀ᶠ eps in l, ∀ x,
        x ∈ Function.support
            (ψeps eps : BHW.OS45FlatCommonChartReal d n -> Complex) ->
          sideLift sgn eps eta0 x ∈ A.carrier ∩ B.carrier := by
    let K0 : Set (BHW.OS45FlatCommonChartReal d n) :=
      tsupport (psi0Flat :
        BHW.OS45FlatCommonChartReal d n -> Complex)
    have hK0_compact : IsCompact K0 := by
      simpa [K0] using hpsi0Flat_compact.isCompact
    have hlocal :
        ∀ y : K0,
          ∀ᶠ eps in nhds (0 : Real),
            sideLift sgn eps eta0 (y.1 + (sgn * eps) • eta0) ∈
              A.carrier ∩ B.carrier := by
      intro y
      have hyA : sideLift sgn 0 eta0 y.1 ∈ A.carrier := hA_zero y.1 y.2
      have hyB : sideLift sgn 0 eta0 y.1 ∈ B.carrier := hB_zero y.1 y.2
      have hcont :
          ContinuousAt
            (fun p : Real × BHW.OS45FlatCommonChartReal d n =>
              sideLift sgn p.1 eta0 (p.2 + (sgn * p.1) • eta0))
            ((0 : Real), y.1) := by
        -- Continuity is by `BHW.os45QuarterTurnCLE.symm.continuous`,
        -- continuity of `BHW.unflattenCfg`, and coordinatewise algebra in
        -- `flatSide`.
        fun_prop
      have hpath :
          Tendsto (fun eps : Real => (eps, y.1))
            (nhds (0 : Real)) (nhds ((0 : Real), y.1)) := by
        simpa using tendsto_id.prod_mk tendsto_const_nhds
      exact (hcont.tendsto.comp hpath).eventually
        ((A.carrier_open.inter B.carrier_open).mem_nhds ⟨hyA, hyB⟩)
    have hnhds :
        ∀ᶠ eps in nhds (0 : Real),
        ∀ y ∈ K0,
          sideLift sgn eps eta0
            (y + (sgn * eps) • eta0) ∈ A.carrier ∩ B.carrier := by
      simpa [K0] using
        hK0_compact.eventually_forall_of_forall_eventually hlocal
    have hwithin :
        ∀ᶠ eps in l,
          ∀ y ∈ K0,
            sideLift sgn eps eta0
              (y + (sgn * eps) • eta0) ∈ A.carrier ∩ B.carrier :=
      hnhds.filter_mono nhdsWithin_le_nhds
    filter_upwards [hwithin] with eps heps x hx
    let y : BHW.OS45FlatCommonChartReal d n :=
      x - (sgn * eps) • eta0
    have hy_support :
        y ∈ Function.support (psi0Flat :
          BHW.OS45FlatCommonChartReal d n -> Complex) := by
      have hx_translate :
          x ∈ Function.support
            (SCV.translateSchwartz (-(sgn * eps) • eta0) psi0Flat :
              BHW.OS45FlatCommonChartReal d n -> Complex) := by
        simpa [hψeps_def eps] using hx
      have hx' :=
        (SCV.mem_support_translateSchwartz_iff
          (-(sgn * eps) • eta0) psi0Flat x).mp hx_translate
      simpa [ψeps, y, sub_eq_add_neg] using hx'
    have hyK : y ∈ K0 := subset_tsupport _ hy_support
    have hx_eq : y + (sgn * eps) • eta0 = x := by
      simp [y, sub_eq_add_neg, add_assoc]
    simpa [hx_eq] using heps y hyK

  filter_upwards [hedge_collar] with eps hmem
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx :
      x ∈ Function.support
        (ψeps eps : BHW.OS45FlatCommonChartReal d n -> Complex)
  · have hzW : sideLift sgn eps eta0 x ∈ A.carrier ∩ B.carrier := hmem x hx
    have hbranch :
      chain.branch j (sideLift sgn eps eta0 x) =
        chain.branch (j + 1) (sideLift sgn eps eta0 x) := by
      exact hEq_inter hzW
    simpa [hbranch]
  · have hψzero :
        ψeps eps x = 0 := by
      exact not_ne_iff.mp (by simpa [Function.mem_support] using hx)
    simp [hψzero]
```

The only name in this block that may become a split helper is the neutral
compact-collar statement used in `hedge_collar`.  Its statement must consume an
explicit `PointedSeedEdge`, the concrete continuous `sideLift`, and the compact
support of `psi0Flat`; it must not mention `Word`, `Wadj`, `Hdiff`,
zero-height equality, or theorem-2 locality.

The source-selector edge sources are handled inside the construction of
`chain.edge` before this induction runs:

```lean
-- Ordinary-sector edge:
--   both carriers sit in ordinary extended-tube windows and both branches
--   agree with `BHW.extendF (bvt_F OS lgc n)` on their carriers.

-- Raw-adjacent-sector edge:
--   the retained `(4.12)` carrier is
--   `{z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ`;
--   its branch is `fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)`.

-- Raw terminal-minus edge:
--   the terminal chart of `chainAdj` is the flat minus chart.  The edge into it
--   is still raw `(4.12)` provenance: first compare the terminal chart with
--   `BSeed412` on the retained source window, then use
--   `extendF_eq_on_forwardTube` only on the eventual positive-height support
--   where `permAct P.τ (sourceSide -1 eps eta0 u)` lies in the forward tube.
--   This produces the terminal normal form needed for scalar cancellation
--   without installing `extendF o permAct` as the incoming seed.
```

Non-circularity gate for the current Hdiff producer: the finite selector used
to prove `hOrd_side_current`/`hAdj_side_current` is upstream of
`hzero_minus`.  It may use ordinary-sector common-model edges, retained
raw-adjacent `(4.12)` edges, and the raw terminal-minus edge just described.
It may not use
`flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM` instantiated
with `hzero_minus`, because that is the downstream EOW seed produced only after
the source-current proof closes.

##### Terminal Flat Normal Forms

The finite induction proves convergence for the terminal chain branch evaluated
at `sideLift`.  Before scalar cancellation, this terminal integral must be
rewritten to the flat common-chart integral `FlatOrd` or `FlatAdj`; this is not
definitionally automatic unless the terminal model field is used.

For the ordinary terminal branch:

```lean
have hOrd_terminal_to_flat :
    ∀ᶠ eps in l,
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        chainOrd.terminalBranch (sideLift (1 : Real) eps eta0 x) *
          ψepsOrd eps x =
      FlatOrd eps := by
  have hterm_collar :
      ∀ᶠ eps in l, ∀ x,
        x ∈ Function.support
            (ψepsOrd eps :
              BHW.OS45FlatCommonChartReal d n -> Complex) ->
          sideLift (1 : Real) eps eta0 x ∈
            chainOrd.terminalCarrier := by
    -- Same compact-collar proof as `hedge_collar`, with `edge.W` replaced by
    -- the terminal carrier and zero-height membership supplied by
    -- `chainOrd.terminal_zero_tsupport_mem`.
    exact
      chainOrd.terminal_sideLift_collar
        (sgn := (1 : Real)) eta0 psi0Flat hpsi0Flat_compact
  filter_upwards [hterm_collar] with eps hmem
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx :
      x ∈ Function.support
        (ψepsOrd eps :
          BHW.OS45FlatCommonChartReal d n -> Complex)
  · have hz :
        sideLift (1 : Real) eps eta0 x ∈ chainOrd.terminalCarrier :=
      hmem x hx
    have hmodel :
        chainOrd.terminalBranch (sideLift (1 : Real) eps eta0 x) =
          BHW.extendF (bvt_F OS lgc n)
            (sideLift (1 : Real) eps eta0 x) :=
      chainOrd.terminal_eq_ordinary_global hz
    -- Unfold `sideLift`, `flatSide`, `FlatOrd`, and
    -- `BHW.os45FlatCommonChartBranch`; for `σ = 1`, the pulled real branch is
    -- exactly `extendF` at the lifted side point.
    simp [FlatOrd, BranchFlatOrd, sideLift, flatSide,
      BHW.os45FlatCommonChartBranch, BHW.os45PulledRealBranch, hmodel]
  · have hψzero :
        ψepsOrd eps x = 0 := by
      exact not_ne_iff.mp (by simpa [Function.mem_support] using hx)
    simp [hψzero]
```

For the adjacent terminal branch the same proof uses the retained raw terminal
model:

```lean
have hAdj_terminal_to_flat :
    ∀ᶠ eps in l,
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        chainAdj.terminalBranch (sideLift (-1 : Real) eps eta0 x) *
          ψepsAdj eps x =
      FlatAdj eps := by
  have hterm_collar :
      ∀ᶠ eps in l, ∀ x,
        x ∈ Function.support
            (ψepsAdj eps :
              BHW.OS45FlatCommonChartReal d n -> Complex) ->
          sideLift (-1 : Real) eps eta0 x ∈
            chainAdj.terminalCarrier := by
    exact
      chainAdj.terminal_sideLift_collar
        (sgn := (-1 : Real)) eta0 psi0Flat hpsi0Flat_compact
  filter_upwards [hterm_collar] with eps hmem
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx :
      x ∈ Function.support
        (ψepsAdj eps :
          BHW.OS45FlatCommonChartReal d n -> Complex)
  · have hz :
        sideLift (-1 : Real) eps eta0 x ∈ chainAdj.terminalCarrier :=
      hmem x hx
    have hmodel :
        chainAdj.terminalBranch (sideLift (-1 : Real) eps eta0 x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (sideLift (-1 : Real) eps eta0 x)) :=
      chainAdj.terminal_eq_raw412_endpoint hz
    have hσAdj : σAdj.symm = P.τ := by
      simp [σAdj]
    simp [FlatAdj, BranchFlatAdj, sideLift, flatSide,
      BHW.os45FlatCommonChartBranch, BHW.os45PulledRealBranch,
      hmodel, hσAdj]
  · have hψzero :
        ψepsAdj eps x = 0 := by
      exact not_ne_iff.mp (by simpa [Function.mem_support] using hx)
    simp [hψzero]
```

The terminal collar proof is the same compactness argument as the edge collar:
zero-height `tsupport psi0Flat` lies in the terminal carrier, the terminal
carrier is open, and the lifted side path is continuous.  If this becomes a
helper, it must be the same neutral compact-collar lemma specialized to an open
carrier; do not create a boundary-value selector for it.

The symbols `chain*.chart`, `chain*.edge`, and
`chain*.chart_zero_tsupport_mem` are implementation-local projections of the
private one-branch chain data.  The displayed `sideLift` is only the terminal
flat/source-side normal form used after the current chain reaches its terminal
flat chart.  The induction itself must use the active path
`gammaOf kind` and the chart-local/edge-local approach families described
above; using the terminal `sideLift` at every chart would make the base case
circular.  If Lean needs support outside the main proof, the only permitted
split is a neutral
finite-induction lemma that consumes an explicit list of charts, pointed seed
edges, zero-height support-in-carrier proofs, and the already proved base
`Tendsto`; it must not mention `Hdiff`, zero-height equality,
common-boundary CLMs, `Word`, `Wadj`, or theorem-2 locality.

#### No-Wrapper Transfer Expansion

The transfer proof should be written as local `have` blocks, not exported as a
new theorem.  For the current compact flat test `phi`, compact cone set `Keta`,
and source cutoff `D`, define the actual side-sheet arguments:

```lean
let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))

let sourceSide (sgn eps : Real)
    (eta : BHW.OS45FlatCommonChartReal d n)
    (u : NPointDomain d n) :
    Fin n -> Fin (d + 1) -> Complex :=
  BHW.os45FlatCommonChartSourceSide
    d n (1 : Equiv.Perm (Fin n)) sgn eps eta u
```

The checked pullback reduces the two branch pairings to the corresponding
`sourceSide` integrals.  The final branch-value unfold is now checked by
`BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF`, and the outgoing
ordinary/adjacent sheet membership is checked by
`BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`.  The combined
integral normal form is checked as
`BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM`.
The support-local outgoing sheet packet is checked as
`BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually`:

```lean
have hBranchPlus_pullback_eventually :
    ∀ᶠ eps in l, ∀ eta in Keta,
      BranchPlusSide eps eta =
        Jflat * integral fun u : NPointDomain d n =>
          BHW.extendF (bvt_F OS lgc n)
            (sourceSide (1 : Real) eps eta u) *
          ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta phi).1 :
            SchwartzNPoint d n) : NPointDomain d n -> Complex) u) := by
  -- `os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM`
  -- with `sigma = 1`, plus the definition of
  -- `os45FlatCommonChartBranch`.

have hBranchMinus_pullback_eventually :
    ∀ᶠ eps in l, ∀ eta in Keta,
      BranchMinusSide eps eta =
        Jflat * integral fun u : NPointDomain d n =>
          Badj_terminal (sourceSide (-1 : Real) eps eta u) *
          ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta phi).1 :
            SchwartzNPoint d n) : NPointDomain d n -> Complex) u) := by
  -- Same checked pullback with `sigma = P.τ.symm * 1`.
  -- `Badj_terminal` is the terminal branch obtained from the raw `(4.12)`
  -- one-branch chain; rewrite it to the flat adjacent branch only after the
  -- terminal endpoint equality has been proved.
```

The two OS-I `(4.14)` leaves are the singleton fixed-direction proof bodies
`hPlus_asymptotic_eta0` and `hMinus_asymptotic_eta0` from the exact transfer
section above.  Their branch provenance is:

```lean
-- Ordinary:
--   `(4.1)` seed -> ordinary one-branch chain -> plus sheet membership ->
--   checked source-side pullback -> moving boundary value ->
--   OS-I `(4.14)` boundary-to-source transfer ->
--   checked `bvt_euclidean_restriction` source normalization.

-- Adjacent:
--   raw `OmegaSeed412/BSeed412` seed -> adjacent one-branch chain ->
--   terminal endpoint equality -> minus sheet membership ->
--   checked source-side pullback -> moving boundary value ->
--   raw OS-I `(4.12)/(4.14)` boundary-to-source transfer ->
--   checked adjacent Wick/source normalization.
```

The final uniform-on-singleton asymptotic statements are then obtained by the
checked singleton bridge, not by a new public theorem:

```lean
have hPlus_asymptotic := by
  simpa [Keta] using
    (SCV.tendstoUniformlyOn_singleton_iff_tendsto
      (F := fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
      (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (p := l) (x := eta0)).2 hPlus_asymptotic_eta0

have hMinus_asymptotic := by
  simpa [Keta] using
    (SCV.tendstoUniformlyOn_singleton_iff_tendsto
      (F := fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
      (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (p := l) (x := eta0)).2 hMinus_asymptotic_eta0
```

The flat real-Jost EOW case split occurs only after these two `have`s: combine
`hPlus_asymptotic`/`hMinus_asymptotic` with the checked source-side common
Schwinger limits, use `SCV.eq_zeroHeight_of_common_sideLimit`, inline the
`integral_sub`/ring rewrite from `AdjEdge = OrdEdge`, and immediately feed the
result to the checked local zero-height flat EOW bridge.  There is no exported
wrapper between the OS-I transfer and the `hadj412` local EOW seed.

Deep Research interaction
`v1_ChdtVklJYXN1V0E2S1AyOG9QbjdlaTZBYxIXbVZJSWFzdVdBNktQMjhvUG43ZWk2QWM`
completed on 2026-05-16 and supports this dependency order: the flat-crossing
compact-test zero is non-circular exactly when it is proved by a direct
Fourier-Laplace/Jost boundary transfer.  The current implementation shape of
that transfer is the side-height form above; a finite-height compact
`chiWick` transform is not the active implementation surface.  Deep Research
interaction
`v1_Chc5VmdJYXEtV01JeUx4TjhQcXBmbndBURIXOVZnSWFxLVdNSXlMeE44UHFwZm53QVE`
completed on 2026-05-16 and explicitly says the finite-height compact
`chiWick` theorem is mathematically false in general; the replacement is the
side-height boundary-limit theorem above.  The proof must not be shortened to
"use `Hdiff` and evaluate at the horizontal edge"; that would turn an EOW
hypothesis into an EOW conclusion.

## All-Overlap Gallery Invariant

For a branch kind `kind`, compare the two terminal branches by building a
finite gallery:

1. Restrict the left terminal chart to a small ball around `z0`.
2. Read the left one-branch chain backwards to the common initial chart.
3. Read the right one-branch chain forwards to the right terminal chart.
4. Restrict the right terminal chart to a small ball around `z0`.

At every prefix stage maintain all pairwise overlap equality, not only
consecutive-step equality:

```lean
prefix_overlap :
  forall i j : Fin (prefixLength + 1),
    Set.EqOn (Gbranch i) (Gbranch j)
      (Gcarrier i inter Gcarrier j)
```

When inserting a new chart `Cnew`, compare it with every older chart whose
carrier intersects it:

```lean
by_cases hne : (Gold i inter Cnew.carrier).Nonempty
case pos =>
  rcases hne with ⟨y, hyi, hynew⟩
  have hseed_i_new :
      exists W : Set (Fin n -> Fin (d + 1) -> Complex),
        IsOpen W /\
        y in W /\
        W <= Gold i inter Cnew.carrier /\
        Set.EqOn (GoldBranch i) Cnew.branch W := by
    -- branch-law seed at y, by one of the three transfer cases above

  rcases hseed_i_new with
    ⟨W, hW_open, hyW, hW_sub, hW_eq⟩
  exact
    SCV.identity_theorem_product_inter_metric_ball_of_eqOn_open
      hW_open hyW hW_sub
      (Gold_holo i) Cnew.holo hW_eq
case neg =>
  intro y hy
  exact False.elim (hne ⟨y, hy⟩)
```

Before the identity-theorem call, rewrite both carriers by their stored
metric-ball fields.  If either selected carrier is not yet a metric ball,
shrink it to a metric ball around the observed point before inserting it into
the prefix family.

For `ordinary41`, `hseed_i_new` reduces to equality with `OrdGlobal` on the
ordinary sheet.

For `adjacent412`, `hseed_i_new` is the genuine hard comparison.  It uses:

```text
OmegaAdj0, BAdj0
adjacent one-branch chain provenance
the adjacent-sector transfer
the flat real-Jost EOW transfer when the comparison crosses the common edge
```

It must not use the downstream deterministic adjacent branch as the initial
germ.

Once the branch-law construction has supplied such a seed for every nonempty
pairwise overlap in the gallery, the SCV identity propagation step is checked:

```lean
have hall_overlap :
    forall i j, Set.EqOn (Gbranch i) (Gbranch j)
      (Gcarrier i inter Gcarrier j) := by
  exact
    SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds
      hGcarrier_ball hGbranch_holo hpair_seed
```

Here `hpair_seed i j hne` is still the genuine OS-I work: it must build the
local open equality seed in the ordinary, adjacent, or flat EOW case.  The
checked SCV lemma only propagates those seeds across metric-ball overlaps; it
does not create the seeds and does not supply any branch provenance.

### Exact Branch-Seed Case Split

The proof-local `hpair_seed` must destruct the stored provenance for the two
charts being compared and choose exactly one of the following three producers.
These are implementation cases inside
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`, not public wrapper
theorems.

Ordinary-sector seed:

```lean
case ordinary_sector =>
  -- Inputs:
  --   Aord : Set.EqOn A.branch OrdGlobal A.carrier
  --   Bord : Set.EqOn B.branch OrdGlobal B.carrier
  --   z0 ∈ A.carrier ∩ B.carrier
  obtain ⟨r, hr_pos, hball_sub⟩ :=
    metric_ball_subset_inter_open hA_open hB_open hzA hzB
  let W := Metric.ball z0 r
  have hW_eq : Set.EqOn A.branch B.branch W := by
    intro z hzW
    exact (Aord (hball_sub hzW).1).trans (Bord (hball_sub hzW).2).symm
  exact ⟨W, Metric.isOpen_ball,
    by simpa [W] using Metric.mem_ball_self hr_pos, hball_sub, hW_eq⟩
```

This case has no flat EOW content and no adjacent branch choice.  It only
uses the ordinary `(4.1)` one-branch chain provenance.

Adjacent-sector seed:

```lean
case adjacent_sector =>
  -- Inputs:
  --   AadjChain, BadjChain : retained one-branch chains that both start from
  --     the genuine `OmegaAdj0/BAdj0` output of `hadj412`;
  --   neither chain starts from the downstream checked adjacent datum.
  --   z0 ∈ A.terminalCarrier ∩ B.terminalCarrier.
  --
  -- Build and consume the finite pointed common-center gallery pair at the
  -- actual overlap point.  The checked consumer does the endpoint retargeting
  -- and returns the open seed directly.
  let Achart : Chart := Achain.terminalChart
  let Bchart : Chart := Bchain.terminalChart
  have hAraw : Adj412RawProvenance Achart :=
    Achain.terminal_adj412_raw
  have hBraw : Adj412RawProvenance Bchart :=
    Bchain.terminal_adj412_raw
  obtain ⟨W, hW_open, hz0W, hW_sub, hW_eq⟩ :=
    adjacent_sector_seed_transport Achart Bchart
      (by simpa [Achart] using hzA)
      (by simpa [Bchart] using hzB)
      hAraw hBraw
  exact ⟨W, hW_open, hz0W, hW_sub, hW_eq⟩
```

This case is no longer a vague appeal to "same chain provenance."  The
implementation must construct the finite pointed common-center gallery pair
inside `hgrid`; the checked consumer returns the open seed that feeds the
identity theorem.  It remains invalid to rewrite any upstream adjacent chart to
`extendF o permAct` before the genuine `(4.12)` Wick trace and horizontal
endpoint trace have been transported.

Flat real-Jost EOW seed:

```lean
case flat_real_jost =>
  -- Inputs:
  --   z0 is on a two-sheet flat overlap near the common real-Jost edge;
  --   Ulocal ⊆ P.V is the source window whose flattened edge contains z0;
  --   h414_integrals is produced inline from the fixed-direction ordinary and
  --     transported adjacent `(4.12)` boundary transfers above.
  let E : Set (BHW.OS45FlatCommonChartReal d n) :=
    BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n)) '' Ulocal
  have hzero_plus :
      forall phi, HasCompactSupport (phi : _ -> Complex) ->
        tsupport (phi : _ -> Complex) <= E ->
        (integral fun x => Fplus0 x * phi x) = Tlocal phi := by
    exact ordinary_zeroHeight_representation_on_E
  have hzero_minus :
      forall phi, HasCompactSupport (phi : _ -> Complex) ->
        tsupport (phi : _ -> Complex) <= E ->
        (integral fun x => Fminus0 x * phi x) = Tlocal phi := by
    intro phi hphi_compact hphiE
    exact (h414_integrals phi hphi_compact hphiE).trans
      (hzero_plus phi hphi_compact hphiE)

  obtain ⟨Wflat, hWflat_open, hWflat_pre, hzWflat,
      hWflat_sub, hWflat_eq⟩ :=
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
      (d := d) hd OS lgc (P := P)
      hE_open hE_sub ys hys_mem hys_li x0 hx0
      Tlocal hzero_plus hzero_minus

  -- Return the ambient equality seed between the ordinary and selected
  -- adjacent initial-sector branches on the two-sector overlap.
  exact ⟨Wflat, hWflat_open, hzWflat, hWflat_sub, hWflat_eq⟩
```

This is the only case that consumes the proof-local OS-I `(4.14)` side-height
branch/source transfer.  It must produce `h414_integrals`, then
`hzero_plus`/`hzero_minus`, before any exported `Hdiff`, common-boundary CLM, or
local `S'_n` branch exists.

Lean-ready branch-seed output:

```lean
have branch_seed
    (kind : BranchKind)
    (Achain Bchain : Chain kind)
    (z0 : Fin n -> Fin (d + 1) -> Complex)
    (hzA : z0 in Achain.terminalCarrier)
    (hzB : z0 in Bchain.terminalCarrier) :
    exists Wkind : Set (Fin n -> Fin (d + 1) -> Complex),
      IsOpen Wkind /\
      z0 in Wkind /\
      Wkind <= Achain.terminalCarrier inter Bchain.terminalCarrier /\
      Set.EqOn Achain.terminalBranch Bchain.terminalBranch Wkind := by
  -- 1. shrink A terminal and B terminal to metric balls centered at z0
  -- 2. reverse Achain, append the common initial seed, then append Bchain
  -- 3. for each nonempty pairwise overlap, call:
  --      ordinary-sector seed,
  --      adjacent-sector seed from hadj412 provenance, or
  --      flat EOW seed from localZeroHeight bridge
  -- 4. apply SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds
  -- 5. glue by SCV.glued_iUnion and restrict back to a small ball at z0
```

This `branch_seed` should remain a local `have`.  A public theorem with this
name would be a wrapper unless its proof eliminates one of the three subproofs
listed above.

After the prefix is complete, glue the finite family proof-locally:

```lean
let G := SCV.glued_iUnion Gcarrier Gbranch
```

Use `SCV.glued_iUnion_eqOn` to rewrite `G` to the left and right retargeted
terminal charts.  Shrinking once inside the two retargeted terminal balls gives
the final branch-kind seed:

```lean
exists Wkind : Set (Fin n -> Fin (d + 1) -> Complex),
  IsOpen Wkind /\
  z0 in Wkind /\
  Wkind <= A.N inter B.N /\
  Set.EqOn A.kindBranch B.kindBranch Wkind
```

Specialize this once to `ordinary41` to get `Word`, and once to `adjacent412`
to get `Wadj`.

## Local Element Packet

For each center `q : Kcx`, the direct proof chooses a local element packet.
This packet is proof-local and should not be exported:

```lean
N : Set (Fin n -> Fin (d + 1) -> Complex)
N_open : IsOpen N
N_preconnected : IsPreconnected N
N_ball : exists r : Real, 0 < r /\ N = Metric.ball q.1 r
center_mem : q.1 in N

Ord : (Fin n -> Fin (d + 1) -> Complex) -> Complex
Adj : (Fin n -> Fin (d + 1) -> Complex) -> Complex
Ord_holo : DifferentiableOn Complex Ord N
Adj_holo : DifferentiableOn Complex Adj N

Cord : Chain ordinary41
Cadj : Chain adjacent412

D := fun z => Adj z - Ord z
D_holo : DifferentiableOn Complex D N
```

Endpoint traces are stored only for endpoint-centered packets:

```text
Wick endpoint: t = 0
Horizontal common-edge endpoint: t = 1
```

If an endpoint lies in a different selected chart, its trace is obtained later
by overlap transport through the proved `overlap_eq`.  The local element
constructor does not assert a global trace formula for every chart.

## Pairwise Overlap Proof

For selected packets `A` and `B`, prove:

```lean
overlap_eq :
  Set.EqOn A.D B.D (A.N inter B.N)
```

Script:

```lean
by_cases hne : (A.N inter B.N).Nonempty
case neg =>
  intro z hz
  exact False.elim (hne ⟨z, hz⟩)

case pos =>
  rcases hne with ⟨z0, hzA, hzB⟩

  have hord_seed := branch_seed ordinary41 A.Cord B.Cord z0 hzA hzB
  have hadj_seed := branch_seed adjacent412 A.Cadj B.Cadj z0 hzA hzB

  rcases hord_seed with
    ⟨Word, hWord_open, hz0Word, hWord_sub, hWord_eq⟩
  rcases hadj_seed with
    ⟨Wadj, hWadj_open, hz0Wadj, hWadj_sub, hWadj_eq⟩

  -- rewrite A.N and B.N by A.N_ball and B.N_ball
  exact
    SCV.identity_theorem_product_inter_metric_ball_sub_of_two_eqOn_open
      hWadj_open hz0Wadj hWadj_sub
      hWord_open hz0Word hWord_sub
      A.Adj_holo A.Ord_holo B.Adj_holo B.Ord_holo
      hWadj_eq hWord_eq
```

Here `branch_seed` is a proof-local finite-gallery induction, not a production
theorem.  It is acceptable to factor out a tiny neutral finite-family gluing
lemma only if the lemma is purely topological or SCV and does not mention OS,
BHW, Figure 2-4, or branch provenance.

## Gluing After All Overlaps

Only after `overlap_eq` is available for all selected packets, define:

```lean
Ucx := iUnion (fun q : Kcx => N q)
Hdiff := SCV.glued_iUnion N D
```

Then use the checked neutral helpers:

```lean
SCV.glued_iUnion_eqOn
SCV.differentiableOn_glued_iUnion
SCV.isConnected_iUnion_of_connected_core
```

Endpoint values of `Hdiff` are obtained by choosing the endpoint-centered
index and applying `SCV.glued_iUnion_eqOn` there.  The compact Wick pairing
zero uses that endpoint-centered trace plus the existing E3 compact-test zero
identity.  The horizontal common-edge trace uses the endpoint-centered
horizontal packet and overlap transport.

## Hdiff Export Shape

The public producer should export exactly the fields consumed by the checked
reducer:

```lean
BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
```

Thus the end of `BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`
should return:

```lean
exists Ucx Hdiff,
  IsOpen Ucx /\
  IsConnected Ucx /\
  (forall u in U, (fun k => wickRotatePoint (u k)) in Ucx) /\
  (forall u in U,
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u)) in Ucx) /\
  DifferentiableOn Complex Hdiff Ucx /\
  (forall phi : SchwartzNPoint d n,
    HasCompactSupport (phi : NPointDomain d n -> Complex) ->
    tsupport (phi : NPointDomain d n -> Complex) <= U ->
    integral (fun u : NPointDomain d n =>
      Hdiff (fun k => wickRotatePoint (u k)) * phi u) = 0) /\
  (forall u in U,
    Hdiff
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))) =
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) -
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)))
```

Derivations:

| Field | Proof source |
| --- | --- |
| `hUcx_open` | `isOpen_iUnion`, from `N_open`. |
| `hUcx_connected` | `SCV.isConnected_iUnion_of_connected_core`, with core `Kcx` and attachment at each selected center. |
| `hwick_mem` | endpoint index `wick_index u hu`, rewritten by `wick_index_eq`, then `center_mem`. |
| `hcommon_mem` | endpoint index `common_index u hu`, rewritten by `common_index_eq`, then `center_mem`. |
| `hHdiff_holo` | `SCV.differentiableOn_glued_iUnion`. |
| `hwick_pairing_zero` | `SCV.glued_iUnion_eqOn` at `wick_index`, endpoint-centered Wick trace, support restriction to `U`, and the existing E3 compact-test zero identity. |
| `hcommon_trace` | `SCV.glued_iUnion_eqOn` at `common_index`, endpoint-centered horizontal trace, and overlap transport. |

Once these fields are exported, call:

```lean
BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
```

to obtain the local horizontal zero representation.  That reducer proves the
pointwise vanishing of `Hdiff` on `Ucx` from the Wick compact-test zero
pairing, then rewrites the horizontal common-edge trace.  It is downstream of
the `Hdiff` producer and must not be used inside the flat transfer that builds
`Wadj`.

## Proof-Local Endpoint Support Contracts

The endpoint subproofs inside `hOrd_boundary_to_source` and
`hAdj_boundary_to_source` may be factored only along the following lines.  These
are local obligations for the current compact test `phi`, not exported wrappers
and not local `forall phi` packets:

The selected one-branch data must carry these proof-local projections:
`terminal_contains_ordinaryCommonEdge`,
`terminal_contains_adjacentCommonEdge`, `terminalBranch_continuousOn`, and the
flat-boundary comparison fields used in the pairing cancellation below.  These
are not theorem-2 wrappers; they are the retained provenance of the ordinary
`(4.1)` and raw-adjacent `(4.12)` chains.

The endpoint DCT assembly is now checked as the neutral SourceSide support
theorem
`BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport`.
In production, the ordinary and raw-adjacent subproofs below should call that
theorem with `F := chain*.terminalBranch`, `U := chain*.terminalCarrier`, and
`φ := ((psi0).1 : SchwartzNPoint d n)` after proving the displayed endpoint
membership.  The expanded script is retained here only as the proof-local audit
of the theorem's inputs.

```lean
have hOrd_endpoint_DCT :
    Tendsto
      (fun eps =>
        ∫ u : NPointDomain d n,
          chainOrd.terminalBranch
            (sourceSide (1 : Real) eps eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u))
      l
      (nhds
        (∫ u : NPointDomain d n,
          chainOrd.terminalBranch
            (sourceSide (1 : Real) 0 eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u))) := by
  have hpsi0_compact :
      HasCompactSupport
        (((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) := by
    simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
      using D.toSchwartzNPointCLM_hasCompactSupport
        (1 : Equiv.Perm (Fin n)) phi
  have hpsi0_support_V :
      tsupport (((psi0).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex) <= P.V := by
    simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
      using D.toSchwartzNPointCLM_tsupport_subset_V
        (1 : Equiv.Perm (Fin n)) phi hphiE
  have hOrd_endpoint_mem :
      forall u in tsupport (((psi0).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex),
        sourceSide (1 : Real) 0 eta0 u in chainOrd.terminalCarrier := by
    intro u hu
    have huV := hpsi0_support_V hu
    rw [BHW.os45FlatCommonChartSourceSide_zero]
    exact chainOrd.terminal_contains_ordinaryCommonEdge u huV
  have hOrd_eventual_collar :=
    BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
      (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (1 : Real))
      (η := eta0) hpsi0_compact.isCompact
      chainOrd.terminalCarrier_open hOrd_endpoint_mem
  have hOrd_pointwise (u : NPointDomain d n) :
      Tendsto
        (fun eps => chainOrd.terminalBranch
          (sourceSide (1 : Real) eps eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u))
        l
        (nhds (chainOrd.terminalBranch
          (sourceSide (1 : Real) 0 eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u))) := by
    by_cases hu : u in tsupport (((psi0).1 : SchwartzNPoint d n) :
      NPointDomain d n -> Complex)
    · exact
        (BHW.tendsto_comp_os45FlatCommonChartSourceSide_nhdsWithin
          (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (1 : Real))
          (η := eta0) (u := u)
          chainOrd.terminalCarrier_open
          chainOrd.terminalBranch_continuousOn
          (hOrd_endpoint_mem u hu)).mul tendsto_const_nhds
    · have hzero := image_eq_zero_of_notMem_tsupport hu
      simpa [hzero]
  rcases
    BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
      (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (1 : Real))
      (η := eta0) hpsi0_compact.isCompact
      chainOrd.terminalCarrier_open hOrd_endpoint_mem
      chainOrd.terminalBranch_continuousOn with
    ⟨MOrd, hMOrd_nonneg, hMOrd_bound⟩
  let g : NPointDomain d n -> Real := fun u =>
    MOrd * ‖((((psi0).1 : SchwartzNPoint d n) :
      NPointDomain d n -> Complex) u)‖
  have hg_int : Integrable g := by
    simpa [g] using
      ((SchwartzMap.integrable
        ((psi0).1 : SchwartzNPoint d n)).norm.const_mul MOrd)
  have hg_bound :
      forallᶠ eps in l, forallᵐ u : NPointDomain d n,
        ‖chainOrd.terminalBranch (sourceSide (1 : Real) eps eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u)‖ <= g u := by
    filter_upwards [hMOrd_bound] with eps hMord
    filter_upwards with u
    by_cases hu : u in tsupport (((psi0).1 : SchwartzNPoint d n) :
      NPointDomain d n -> Complex)
    · calc
        ‖chainOrd.terminalBranch (sourceSide (1 : Real) eps eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u)‖
            = ‖chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u)‖ *
              ‖((((psi0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u)‖ := by
                simp [norm_mul]
        _ <= MOrd * ‖((((psi0).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u)‖ :=
            mul_le_mul_of_nonneg_right (hMord u hu) (norm_nonneg _)
    · have hzero :
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u) = 0 :=
        image_eq_zero_of_notMem_tsupport hu
      simp [g, hzero, hMOrd_nonneg]
  have hOrd_aestrongly :
      forallᶠ eps in l,
        AEStronglyMeasurable (fun u : NPointDomain d n =>
          chainOrd.terminalBranch (sourceSide (1 : Real) eps eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u)) := by
    filter_upwards [hOrd_eventual_collar] with eps heps
    exact
      BHW.aestronglyMeasurable_zeroExtension_mul_of_compactSupport
        (K := tsupport (((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex))
        hpsi0_compact.isCompact
        (chainOrd.terminalBranch_continuousOn.comp
          (BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
            (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (1 : Real))
            (eps := eps) (η := eta0)).continuousOn heps)
        ((psi0).1 : SchwartzNPoint d n).continuous.continuousOn
        (by intro u hu; simp [image_eq_zero_of_notMem_tsupport hu])
  exact
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := g) hOrd_aestrongly hg_bound hg_int hOrd_pointwise

have hAdj_endpoint_DCT :
    Tendsto
      (fun eps =>
        ∫ u : NPointDomain d n,
          chainAdj.terminalBranch
            (sourceSide (-1 : Real) eps eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u))
      l
      (nhds
        (∫ u : NPointDomain d n,
          chainAdj.terminalBranch
            (sourceSide (-1 : Real) 0 eta0 u) *
          ((((psi0).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u))) := by
  have hpsi0_compact :
      HasCompactSupport
        (((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) :=
    by
      simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
        using D.toSchwartzNPointCLM_hasCompactSupport
          (1 : Equiv.Perm (Fin n)) phi
  have hpsi0_support_V :
      tsupport
        (((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) <= P.V := by
    simpa [psi0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
      using D.toSchwartzNPointCLM_tsupport_subset_V
        (1 : Equiv.Perm (Fin n)) phi hphiE
  have hAdj_endpoint_mem :
      forall u in tsupport (((psi0).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex),
        sourceSide (-1 : Real) 0 eta0 u in chainAdj.terminalCarrier := by
    intro u hu
    have huV := hpsi0_support_V hu
    rw [BHW.os45FlatCommonChartSourceSide_zero]
    exact chainAdj.terminal_contains_adjacentCommonEdge u huV
  simpa [sourceSide] using
    BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
      (d := d) (n := n)
      (ρperm := (1 : Equiv.Perm (Fin n))) (sgn := (-1 : Real))
      (η := eta0)
      (U := chainAdj.terminalCarrier)
      (F := chainAdj.terminalBranch)
      chainAdj.terminalCarrier_open
      chainAdj.terminalBranch_continuousOn
      hpsi0_compact
      ((psi0).1 : SchwartzNPoint d n).continuous
      hAdj_endpoint_mem

have hOrd_currentTest_schwinger :
    Word (((D.toZeroDiagonalCLM
      (1 : Equiv.Perm (Fin n)) phi).1 : SchwartzNPoint d n)) =
      OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi) := by
  -- Current-test ordinary Wick-trace normalization, proof-local.  This is
  -- deliberately specialized to the in-scope `phi`; do not implement a reusable
  -- `forall phi` packet or exported terminal-boundary equality theorem.
  let ψZ := D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi
  have hψV :
      tsupport (((ψZ).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex) <= P.V := by
    simpa [ψZ, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
      using
        D.toSchwartzNPointCLM_tsupport_subset_V
          (1 : Equiv.Perm (Fin n)) phi hphiE
  have hWord_bvt :
      Word ((ψZ).1 : SchwartzNPoint d n) =
        bvt_W OS lgc n ((ψZ).1 : SchwartzNPoint d n) := by
    -- Retained ordinary `(4.1)` one-branch provenance.  This is proved in the
    -- current proof body by the fixed-test finite induction with base
    -- `ordinary41_fixed_test_boundaryValue_extendF`; do not store it as a
    -- `terminal_boundaryCLM_eq_bvt_W` field on the chain.
    exact hWord_bvt_from_ordinary41_inline ((ψZ).1 : SchwartzNPoint d n)
  have hbvt_schwinger :
      bvt_W OS lgc n ((ψZ).1 : SchwartzNPoint d n) = OS.S n ψZ := by
    -- The ordinary Euclidean restriction is the only Schwinger normalization
    -- used on this side.  The support condition is already in `hψV`; no
    -- common-boundary packet or `Hdiff` exists here.
    simpa [ψZ] using
      (bvt_euclidean_restriction (d := d) OS lgc n ψZ).symm
  exact hWord_bvt.trans hbvt_schwinger

have hAdj_currentTest_endpointCarrier :
    Wadj (((D.toZeroDiagonalCLM
      (1 : Equiv.Perm (Fin n)) phi).1 : SchwartzNPoint d n)) =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.os45QuarterTurnConfig
            (fun k => wickRotatePoint (u (P.τ k)))) *
          (D.toSchwartzNPointCLM
            (1 : Equiv.Perm (Fin n)) phi : NPointDomain d n -> Complex) u := by
  -- Current-test common-edge carrier normalization, proof-local.  The
  -- zero-height source-side endpoint is the inverse quarter-turn of the
  -- horizontal common edge; after applying `permAct`, the checked coordinate
  -- lemma gives the quarter-turned adjacent Wick carrier, not the unturned Wick
  -- point.  The carrier-to-Wick pairing equality is proved separately below.
  let ψZ := D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi
  have hψV :
      tsupport (((ψZ).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex) <= P.V := by
    simpa [ψZ, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
      using
        D.toSchwartzNPointCLM_tsupport_subset_V
          (1 : Equiv.Perm (Fin n)) phi hphiE
  let Ωseed :=
    {z : Fin n -> Fin (d + 1) -> Complex |
      BHW.permAct (d := d) P.τ z in BHW.ForwardTube d n} ∩ H.ΩJ
  let Bseed := fun z =>
    bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
  have hWadj_endpoint :
      Wadj ((ψZ).1 : SchwartzNPoint d n) =
        ∫ u : NPointDomain d n,
          chainAdj.terminalBranch
            (sourceSide (-1 : Real) 0 eta0 u) *
          (((ψZ).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u := by
    -- Uniqueness of limits for the current compact test.  The fixed-test
    -- selected boundary value is `hAdj_fixed_psi0`; the independent endpoint
    -- computation is `hAdj_endpoint_DCT`.  This is still before any carrier
    -- pairing cancellation and before any common-boundary conclusion.
    simpa [ψZ, psi0] using
      tendsto_nhds_unique hAdj_fixed_psi0 hAdj_endpoint_DCT
  have hraw_endpoint_pairing :
      (∫ u : NPointDomain d n,
          chainAdj.terminalBranch
            (sourceSide (-1 : Real) 0 eta0 u) *
          (((ψZ).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u) =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n
            (BHW.os45QuarterTurnConfig
              (fun k => wickRotatePoint (u (P.τ k)))) *
            (((ψZ).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u := by
    have hpoint :
        ∀ᵐ u : NPointDomain d n,
          chainAdj.terminalBranch
              (sourceSide (-1 : Real) 0 eta0 u) *
            (((ψZ).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u =
          bvt_F OS lgc n
              (BHW.os45QuarterTurnConfig
                (fun k => wickRotatePoint (u (P.τ k)))) *
            (((ψZ).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u := by
      filter_upwards with u
      by_cases hu :
          u in tsupport (((ψZ).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex)
      · have huV : u in P.V := hψV hu
        have hsource_zero :
            sourceSide (-1 : Real) 0 eta0 u =
              (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) := by
          simpa [sourceSide] using
            BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
              (d := d) (n := n)
              (ρperm := (1 : Equiv.Perm (Fin n)))
              (sgn := (-1 : Real)) (η := eta0) (u := u)
        have hbranch :
            chainAdj.terminalBranch
                (sourceSide (-1 : Real) 0 eta0 u) =
              Bseed
                ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u))) := by
          -- Raw `(4.12)` terminal provenance transported by `chainAdj`.
          -- The comparison to the raw seed is produced by the retained
          -- one-branch gallery, not by a downstream deterministic seed.
          simpa [Ωseed, Bseed, hsource_zero] using
            chainAdj.terminal_eq_raw412_seed
              (sourceSide (-1 : Real) 0 eta0 u)
        have hperm_quarter :
            BHW.permAct (d := d) P.τ
                ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u))) =
              BHW.os45QuarterTurnConfig
                (fun k => wickRotatePoint (u (P.τ k))) := by
          simpa using
            BHW.permAct_os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick
              (d := d) (n := n)
              (τ := P.τ) (ρperm := (1 : Equiv.Perm (Fin n))) (u := u)
        simp [Bseed, hbranch, hperm_quarter]
      · have hzero :
            (((ψZ).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u = 0 :=
          image_eq_zero_of_notMem_tsupport hu
        simp [hzero]
    exact integral_congr_ae hpoint
  simpa [ψZ, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
    using hWadj_endpoint.trans hraw_endpoint_pairing

have hAdj_currentTest_adjacentWick :
    Wadj (((D.toZeroDiagonalCLM
      (1 : Equiv.Perm (Fin n)) phi).1 : SchwartzNPoint d n)) =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
          (D.toSchwartzNPointCLM
            (1 : Equiv.Perm (Fin n)) phi : NPointDomain d n -> Complex) u := by
  -- Current-test raw-adjacent Wick-trace normalization, proof-local.  This is
  -- not obtained from the zero-height `sourceSide` endpoint above.  Use the
  -- retained raw `(4.12)` one-branch provenance at the adjacent Wick endpoint
  -- (`t = 0`), compare the terminal chart to the raw seed
  -- `OmegaSeed412/BSeed412`, and only then rewrite the seed value to
  -- `bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k)))` on the support of
  -- the current compact test.
  let ψZ := D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi
  have hψV :
      tsupport (((ψZ).1 : SchwartzNPoint d n) :
        NPointDomain d n -> Complex) <= P.V := by
    simpa [ψZ, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
      using
        D.toSchwartzNPointCLM_tsupport_subset_V
          (1 : Equiv.Perm (Fin n)) phi hphiE
  have hWadj_wick_endpoint :
      Wadj ((ψZ).1 : SchwartzNPoint d n) =
        ∫ u : NPointDomain d n,
          chainAdj.terminalBranch
            (fun k => wickRotatePoint (u k)) *
          (((ψZ).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u := by
    -- Proof-local current-test specialization of the adjacent Wick endpoint
    -- trace carried by the retained raw `(4.12)` chain.  This uses the
    -- endpoint-centered Wick chart, not `sourceSide (-1) 0`.
    exact chainAdj.currentTest_adjacentWick_trace ((ψZ).1 : SchwartzNPoint d n) hψV
  have hraw_wick_pairing :
      (∫ u : NPointDomain d n,
          chainAdj.terminalBranch
            (fun k => wickRotatePoint (u k)) *
          (((ψZ).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u) =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
            (((ψZ).1 : SchwartzNPoint d n) :
              NPointDomain d n -> Complex) u := by
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu :
        u in tsupport (((ψZ).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex)
    · have huV : u in P.V := hψV hu
      have hbranch :
          chainAdj.terminalBranch (fun k => wickRotatePoint (u k)) =
            bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) :=
        chainAdj.terminal_adjacentWick_trace u huV
      rw [hbranch]
    · have hzero :
          (((ψZ).1 : SchwartzNPoint d n) :
            NPointDomain d n -> Complex) u = 0 :=
        image_eq_zero_of_notMem_tsupport hu
      simp [hzero]
  simpa [ψZ, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM]
    using hWadj_wick_endpoint.trans hraw_wick_pairing

have hOrd_carrier_pairing :
    (∫ u : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.os45QuarterTurnConfig
            (fun k => wickRotatePoint (u k))) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u)) =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u) := by
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n
  let psi0Flat :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm)
      ((psi0).1 : SchwartzNPoint d n)
  let pullFlatToSource :
      SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
        ->L[Complex] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
  let carrierPairing : Complex := ∫ u : NPointDomain d n,
    bvt_F OS lgc n
      (BHW.os45QuarterTurnConfig (fun k => wickRotatePoint (u k))) *
    ((((psi0).1 : SchwartzNPoint d n) :
      NPointDomain d n -> Complex) u)
  let wickPairing : Complex := ∫ u : NPointDomain d n,
    bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
    ((((psi0).1 : SchwartzNPoint d n) :
      NPointDomain d n -> Complex) u)
  let WordFlat :
      SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
        ->L[Complex] Complex :=
    J • (Word.comp pullFlatToSource)
  have hJ_ne : J ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
  have hWord_carrier :
      WordFlat psi0Flat = J * carrierPairing := by
    calc
      WordFlat psi0Flat = J * Word ((psi0).1 : SchwartzNPoint d n) := by
        have hpull :
            pullFlatToSource psi0Flat =
              ((psi0).1 : SchwartzNPoint d n) := by
          ext u
          simp [pullFlatToSource, psi0Flat]
        simp [WordFlat, hpull]
      _ = J * carrierPairing := by
        rw [hWord_endpoint, hOrd_endpoint_as_carrier]
  have hWord_wick :
      WordFlat psi0Flat = J * wickPairing := by
    have hWord_schwinger :
      Word ((psi0).1 : SchwartzNPoint d n) =
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi) := by
      -- Ordinary `(4.1)` Wick trace, transported along `chainOrd`.
      exact hOrd_currentTest_schwinger
    have hwick_schwinger :
        wickPairing =
          OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi) := by
      simpa [wickPairing, psi0] using
        (bvt_euclidean_restriction (d := d) OS lgc n
          (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi)).symm
    calc
      WordFlat psi0Flat = J * Word ((psi0).1 : SchwartzNPoint d n) := by
        have hpull :
            pullFlatToSource psi0Flat =
              ((psi0).1 : SchwartzNPoint d n) := by
          ext u
          simp [pullFlatToSource, psi0Flat]
        simp [WordFlat, hpull]
      _ = J * wickPairing := by
        rw [hWord_schwinger, hwick_schwinger]
  exact mul_left_cancel₀ hJ_ne (hWord_carrier.symm.trans hWord_wick)

have hAdj_carrier_pairing :
    (∫ u : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.os45QuarterTurnConfig
            (fun k => wickRotatePoint (u (P.τ k)))) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u)) =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n
          (fun k => wickRotatePoint (u (P.τ k))) *
        ((((psi0).1 : SchwartzNPoint d n) :
          NPointDomain d n -> Complex) u) := by
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n
  let psi0Flat :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm)
      ((psi0).1 : SchwartzNPoint d n)
  let pullFlatToSource :
      SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
        ->L[Complex] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex e
  let carrierAdjPairing : Complex := ∫ u : NPointDomain d n,
    bvt_F OS lgc n
      (BHW.os45QuarterTurnConfig
        (fun k => wickRotatePoint (u (P.τ k)))) *
    ((((psi0).1 : SchwartzNPoint d n) :
      NPointDomain d n -> Complex) u)
  let wickAdjPairing : Complex := ∫ u : NPointDomain d n,
    bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
    ((((psi0).1 : SchwartzNPoint d n) :
      NPointDomain d n -> Complex) u)
  let WadjFlat :
      SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex
        ->L[Complex] Complex :=
    J • (Wadj.comp pullFlatToSource)
  have hJ_ne : J ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
  have hWadj_carrier :
      WadjFlat psi0Flat = J * carrierAdjPairing := by
    calc
      WadjFlat psi0Flat = J * Wadj ((psi0).1 : SchwartzNPoint d n) := by
        have hpull :
            pullFlatToSource psi0Flat =
              ((psi0).1 : SchwartzNPoint d n) := by
          ext u
          simp [pullFlatToSource, psi0Flat]
        simp [WadjFlat, hpull]
      _ = J * carrierAdjPairing := by
        rw [hWadj_endpoint, hAdj_endpoint_as_carrier]
  have hWadj_wick :
      WadjFlat psi0Flat = J * wickAdjPairing := by
    have hWadj_adjWick :
        Wadj ((psi0).1 : SchwartzNPoint d n) = wickAdjPairing := by
      -- Raw `(4.12)` Wick trace, transported along `chainAdj`.
      exact hAdj_currentTest_adjacentWick
    calc
      WadjFlat psi0Flat = J * Wadj ((psi0).1 : SchwartzNPoint d n) := by
        have hpull :
            pullFlatToSource psi0Flat =
              ((psi0).1 : SchwartzNPoint d n) := by
          ext u
          simp [pullFlatToSource, psi0Flat]
        simp [WadjFlat, hpull]
      _ = J * wickAdjPairing := by
        rw [hWadj_adjWick]
  exact mul_left_cancel₀ hJ_ne (hWadj_carrier.symm.trans hWadj_wick)
```

With these four leaves, `hOrd_boundary_to_source` and
`hAdj_boundary_to_source` are mechanical uniqueness-of-limits arguments: use
`tendsto_nhds_unique` between `h*_fixed psi0` and `h*_endpoint_DCT`, then
rewrite the endpoint integral to the carrier pairing pointwise by the carrier
identity, and finally apply `h*_carrier_pairing`.

### Stage-A Direct-Producer Contract

As of 2026-05-17, this transcript is the direct-producer contract for the
strict Stage-A E-to-R implementation.  It is not a closure declaration: the
producer remains open until the listed objects, especially the two
branch/source side-height transfers, are actually built in the direct body.
The implementation should enter that body and build the following local
objects in this order, with no public theorem wrapper or assumption packet
inserted between them:

```lean
-- 1. Concrete OS-I seeds.
OmegaOrd0 / BOrd0
OmegaSeed412 / BSeed412

-- 2. One-branch chains and their fixed translated-boundary selector data.
chainOrd, Word
chainAdj, Wadj

-- 3. Horizontal compact-test zero.
hPlus_asymptotic_eta0
hMinus_asymptotic_eta0
hPlus_asymptotic
hMinus_asymptotic
hEdge_eq
hflat_zero
hzero_plus
hzero_minus

-- 4. Local branch-law grid and germ construction.
hgrid : PointedCommonCenterGalleryPair leftTerminal rightTerminal z0
overlap_eq
Ucx, Hdiff
```

Every name in that list is proof-local.  The scripts for the support leaves
are above; the hard mathematical bodies are the ordinary and retained
raw-adjacent branch/source side-height transfers feeding `hzero_plus` and
`hzero_minus`.  If Lean exposes a missing support fact, the allowed split is
only a narrow neutral support lemma whose statement is already named in this
transcript.  It is not acceptable to add a public side-transfer theorem,
`AdjEdge = OrdEdge` theorem, `Wadj` packet, `Hdiff` wrapper, common-boundary
CLM wrapper, source-oriented continuation detour, or theorem-2 wrapper.

## Lean-Start Checklist

Start Lean for `BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` only
when the proof script can point to these exact in-proof objects.  Because the
checked SourceSide support imports through `OSToWightmanLocalityOS45BHWJostLocal.lean`,
the theorem should be implemented in a downstream narrow companion such as
`OSToWightmanLocalityOS45Figure24Hdiff.lean`, not by importing
`OSToWightmanLocalityOS45SourceSideMoving.lean` back into `BHWJostLocal`.

| Object | Needed before Lean |
| --- | --- |
| `OmegaOrd0`, `BOrd0` | Ordinary initial chart and trace to `OrdGlobal`. |
| `OmegaSeed412`, `BSeed412` | Checked raw `(4.12)` seed window at `zadj`, not at `zord`. |
| Raw source-current adjacent chart | Checked directly from `OmegaSeed412/BSeed412` at `gammaAdjSeed 0 = BHW.permAct P.τ (gammaOrd 0)` by `BHW.OS45BHWJostHullData.OS412SeedWindow_pointedChart`; this is the input for `hAdj_fixed_selected` and does not require `hadj412`, `OmegaAdj0`, or `BAdj0`.  Do not read this as `gammaOrd 0 ∈ OmegaSeed412`; that is formally false. |
| Downstream `hadj412`, producing `OmegaAdj0`, `BAdj0` | Built only after the source-current leaves have produced `hzero_plus`/`hzero_minus` and the flat EOW seed is available; this later circuit supplies the adjacent Wick trace and usable adjacent branch object for the overlap-grid stage, not for proving the current `hzero_minus` leaf. |
| Initial metric-ball chart constructors | Checked for the ordinary Wick chart, corrected `(4.12)` seed chart, and raw-seed two-sheet shrink by `BHW.OS45BHWJostHullData.ordinaryWick_metricBallChartInWindow`, `BHW.OS45BHWJostHullData.OS412SeedWindow_metricBallChartInWindow`, and `BHW.OS45BHWJostHullData.OS412SeedWindow_initialSectorOverlap_metricBallChart`. |
| Endpoint metric-ball chart constructors | Checked for the ordinary and adjacent horizontal common-edge endpoint charts by `BHW.OS45BHWJostHullData.ordinaryCommonEdge_metricBallChartInWindow` and `BHW.OS45BHWJostHullData.adjacentCommonEdge_metricBallChartInWindow`; private pointed adapters for both endpoint chart shapes are checked in `OSToWightmanLocalityOS45Figure24Hdiff.lean`. |
| Endpoint difference metric-ball chart | Checked by `BHW.OS45BHWJostHullData.commonEdgeDifference_metricBallChartInWindow`; it gives the final horizontal `Adj - Ord` trace on an exact metric-ball carrier, and the private pointed adapter for the eventual Hdiff chart is checked in `OSToWightmanLocalityOS45Figure24Hdiff.lean`. |
| Metric-ball all-overlap propagation | Checked by `SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds`; it turns proof-local seeds on every nonempty pairwise overlap into full pairwise branch equality. |
| Ambient local zero-height flat EOW bridge | Checked by `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`; it transports local flat zero-height pairings to an ambient open seed in `ExtendedTube d n inter permutedExtendedTubeSector d n P.τ`. |
| Translated source-to-flat Jacobian algebra | Checked by `BHW.os45CommonEdgeFlatCLE_integral_comp_shift`; this is the real-translation plus CLE change of variables behind `x = e u ± eps • eta`. |
| Shifted/signed side cutoff removal and moving-test inputs | Checked by `BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge`, `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_of_tsupport_subset_edge`, `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_eventually`, and `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually`; it discharges the pointwise cutoff-removal part of the side-height coordinate pullback after support has been shrunk.  The actual common-compact-support and zeroth-seminorm inputs are checked by `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually` and `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero`, and the fixed-endpoint-to-moving-test convergence is checked by `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport`.  Its split uses `BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport` and `BHW.eventually_integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport` internally. |
| Signed side-height branch/source pullback | Checked by `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shift`, `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shiftedCLM`, `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM`, `BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM`, and the fixed-test workhorse `BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest`; it packages the translated CLE Jacobian, cutoff-removal algebra, and test-translation cancellation for the side tests without assuming any OS-I `(4.14)` boundary-value limit. |
| Source-side side-sheet argument | Checked by `BHW.os45FlatCommonChartSourceSide`, `BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF`, and `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`; it names the exact source configuration obtained by undoing the quarter-turn, unfolds the flat branch value to `extendF`, and identifies the outgoing sheet-domain condition. |
| Eventual source-side sheet membership | Checked by `BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually`; for small positive side height, shifted support points land on the ordinary plus and raw-adjacent minus outgoing sheets. |
| Side branch integrability | Checked by `BHW.os45FlatCommonChart_branch_shifted_mul_integrable` and `BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually`; side-domain membership plus compact support gives the integrability hypothesis needed by the pullback theorem. |
| Inverse-CLE fixed-test support | Checked by `BHW.hasCompactSupport_comp_os45CommonEdgeFlatCLE_symm`, `BHW.tsupport_comp_os45CommonEdgeFlatCLE_symm_subset_edgeSet`, and bundled as `BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM_flatPullback_support`; these support-only lemmas supply compact support and edge-set support for the auxiliary `psi0Flat` in the scalar-cancellation block. |
| Fixed source-side scalar cancellation | Checked support theorem retained as fallback only: `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest` applies after a genuine fixed flat translated-test limit has already been selected.  It is not the active base for the live `hOrd_side_current`/`hAdj_side_current` holes and must not be used to resurrect a fabricated `eta0` fixed-ray route. |
| Direct source-current selection | Active proof-local OS-I ingredient for the two live holes, corrected 2026-05-18.  The finite chart induction does **not** propagate the moving current limits themselves through the ordinary `gammaOrd` and raw `gammaAdjSeed` chains.  It first proves the fixed flat translated-boundary selectors `hflatOrd_selected` and `hflatAdj_selected` for `psi0 := (D.toZeroDiagonalCLM 1 phi).1`, using `psi0Flat`, the checked inverse-CLE support packet, and chart-local fixed approach families.  Ordinary starts from the genuine `(4.1)` incoming fixed OS-I ray; raw adjacent starts from `OmegaSeed412/BSeed412` at `gammaAdjSeed 0 = BHW.permAct P.τ (gammaOrd 0)`, not from the downstream `hadj412` branch and not from `gammaOrd 0 ∈ OmegaSeed412`.  Each edge promotes a `PointedSeedEdge` to carrier-intersection equality by `PointedMetricBranchChart.eqOn_inter_of_seed`, then uses compact collar control for that edge's fixed approach and `integral_congr_ae`.  The terminal `sideLift`/flat-source rewrite and scalar cancellation by `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest` occur only after the terminal chart has been reached.  The live moving current tests enter later through the already present endpoint DCTs, after the fixed endpoint value has been identified with `Lcur`. |
| Endpoint continuity/DCT | Checked SourceSide support theorem `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport`; endpoint membership comes from `terminal_contains_ordinaryCommonEdge`/`terminal_contains_adjacentCommonEdge`, and the theorem packages compact-collar membership/bounds, pointwise convergence, compact-support integrability, fixed-height continuity, and zero-extension measurability.  This computes the fixed-test side-height limit at `eps = 0` and does not assume either asymptotic transfer. |
| Zero-height endpoint normal forms | Checked coordinate identities now include `BHW.os45FlatCommonChartSourceSide_zero`, `BHW.permAct_os45FlatCommonChartSourceSide_zero`, `BHW.os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick`, `BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge`, and `BHW.permAct_os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick`.  These identify the zero-height endpoint with the quarter-turned carrier over the horizontal common edge; they do not identify that carrier with the unturned Wick point.  The pairing identity defines the plain CLE pullback `pullFlatToSource := SchwartzMap.compCLMOfContinuousLinearEquiv Complex e` and then `WordFlat := J • (Word.comp pullFlatToSource)` and `WadjFlat := J • (Wadj.comp pullFlatToSource)` locally.  The equality `pullFlatToSource psi0Flat = psi0` is an explicit CLE inverse calculation; only after the carrier and Wick endpoint traces are separately selected do the scripts cancel the nonzero Jacobian `BHW.os45CommonEdgeFlatJacobianAbs n`.  The adjacent side uses only retained raw `(4.12)` terminal provenance; no downstream deterministic adjacent seed, `Hdiff`, common-boundary CLM, or chain-level flat-boundary wrapper is in scope. |
| `Chain ordinary41` | Terminal ordinary branch plus metric balls and seeds, with terminal chart typed as `Chart`. |
| `Chain adjacent412` | Terminal adjacent branch plus metric balls and retained raw `(4.12)` provenance, with terminal chart typed as `Chart`. |
| finite chain assembly along `gamma` | Proof-local reachability argument on `unitInterval`: for source-current selectors, build the initial raw/ordinary chain and use only ordinary or retained raw-adjacent local transfers as the `hlocal` input to `SCV.reachable_eq_univ_of_local_symmetric_extension`; the flat plus/minus EOW transfer is downstream after zero-height pairings. |
| `hgrid` restricted-gallery contract | Proof-local finite pointed common-center gallery pair comparing two adjacent retained charts after endpoint retargeting.  The transcript carries raw adjacent provenance explicitly; after the source-current leaves close, every edge seed is a checked `PointedSeedEdge` from retained raw provenance, ordinary common-model overlap, or the post-source-current flat real-Jost EOW seed, and the needed flat-edge orientation reversal is checked privately as `PointedSeedEdge.symm`. |
| `local_transfer ordinary-sector` | Seed by equality with `OrdGlobal`. |
| `local_transfer adjacent-sector` | Seed from retained transported `(4.12)` provenance; no deterministic adjacent branch. |
| `local_transfer flat` | Non-circular flat EOW packet: first prove the local zero-height pairings `hzero_plus` and `hzero_minus` by the ordinary and raw-adjacent branch/source asymptotic transfers plus the checked common source limit; then use the checked ambient local zero-height bridge directly.  Source/CLE/Jacobian facts are coordinate audits only. |
| ordinary branch/source transfer | Proof-local OS-I `(4.14)` current transfer for the ordinary `(4.1)` element; implement the direct `OrdBase`/`OrdTerminal` proof in `docs/theorem2_source_current_selector_transcript.md`, with no public side-transfer wrapper. |
| raw-adjacent branch/source transfer | Proof-local OS-I `(4.14)` current transfer for the retained raw adjacent `(4.12)` element; implement the direct `AdjBase`/`AdjTerminal` proof through `gammaAdjSeed` and `OmegaSeed412/BSeed412`.  `extendF o permAct` may be used only after the raw seed has reached the terminal chart and the current support is on the raw forward-tube sheet. |
| `branch_seed ordinary41` | Proof-local all-overlap finite-gallery induction yielding `Word`. |
| `branch_seed adjacent412` | Proof-local all-overlap finite-gallery induction yielding `Wadj`. |
| `overlap_eq` | Difference equality on `A.N inter B.N` using the checked two-seed SCV helper. |
| `Ucx`, `Hdiff` | Direct gluing after all pairwise overlaps are proved. |

Lean-entry status, corrected 2026-05-17: the checked support entries and the
proof-local transcript now identify the direct implementation route: enter the
Hdiff producer body by constructing `hadj412`, `chainOrd`, `chainAdj`, the
side-height leaves, and the pointed `hgrid` seeds in that order.  During
implementation, if a neutral checked support lemma is missing, add only that
neutral lemma with the exact statement above; otherwise proceed inside the
direct Hdiff producer body.  Do not add a public wrapper theorem or a packet
whose fields assume the chains, `Word`, `Wadj`, or the zero-height pairings.
