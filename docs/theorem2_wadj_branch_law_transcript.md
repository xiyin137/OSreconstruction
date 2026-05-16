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
`hsource_zero_rep` source representation, which the checked source-to-flat
reducer turns into the local zero-height bridge inputs.

## Adjacent 4.12 Seed-To-Wick Circuit

This is the mathematical gap that must be closed before starting the public
`Hdiff` theorem.  It is a proof-local block, not a new wrapper theorem.

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
3. **Flat common-edge crossover from `padj` to `pord`.**  Prove the
   source-window zero representation `hsource_zero_rep` for the horizontal
   pulled-branch difference of the current ordinary and transported adjacent
   analytic elements, convert it to local zero-height pairings by the checked
   source-to-flat reducer, and call
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

### What Is Still Unproved In `hadj412`

The `hadj412` circuit is not Lean-ready until these internal subproofs are
expanded in the proof body:

1. `adjacent_sector_seed_transport`: given two metric-ball charts inside the
   selected adjacent sheet, both carrying the retained continuation of
   `BSeed412`, produce a nonempty complex-open equality seed on their overlap.
   This is the local Hall-Wightman analytic-element uniqueness step.  It is
   not a topological connectedness argument and it is not the deterministic
   `extendF` after permutation.
2. proof-local flat zero-height pairing block: for a local flat edge window
   `E`, construct `Tlocal`, `hzero_plus`, and `hzero_minus` from
   `hsource_zero_rep`, the OS-I `(4.14)` source common-boundary theorem for
   the ordinary `(4.1)` side and genuine adjacent `(4.12)` side.  The checked
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

The adjacent transport datum for a chart is not just membership in
`AdjSheet`.  It must remember the raw `(4.12)` seed, the current chart, and the
finite analytic-element path joining them.

Proof-local packet:

```lean
structure Adj412ChartProv
    (C : Set (Fin n -> Fin (d + 1) -> Complex))
    (B : (Fin n -> Fin (d + 1) -> Complex) -> Complex) : Prop where
  carrier_ball :
    exists c r, 0 < r /\ C = Metric.ball c r
  carrier_sub :
    C <= BHW.ExtendedTube d n \cap
      BHW.permutedExtendedTubeSector d n P.τ \cap H.OmegaJ
  holo :
    DifferentiableOn Complex B C
  seed_gallery :
    exists (m : Nat)
      (Gcarrier : Fin (m + 1) ->
        Set (Fin n -> Fin (d + 1) -> Complex))
      (Gbranch : Fin (m + 1) ->
        (Fin n -> Fin (d + 1) -> Complex) -> Complex),
      Gcarrier 0 = OmegaSeed412 /\
      Gbranch 0 = BSeed412 /\
      Gcarrier (Fin.last m) = C /\
      Gbranch (Fin.last m) = B /\
      (forall j, IsOpen (Gcarrier j)) /\
      (forall j, exists c r, 0 < r /\ Gcarrier j = Metric.ball c r) /\
      (forall j, DifferentiableOn Complex (Gbranch j) (Gcarrier j)) /\
      (forall j, Gcarrier j <=
        BHW.ExtendedTube d n \cap
          BHW.permutedExtendedTubeSector d n P.τ \cap H.OmegaJ) /\
      (forall j : Fin m,
        exists Wj, IsOpen Wj /\ Wj.Nonempty /\
          Wj <= Gcarrier (Fin.castSucc j) \cap Gcarrier (Fin.succ j) /\
          Set.EqOn (Gbranch (Fin.castSucc j))
            (Gbranch (Fin.succ j)) Wj)
```

Given two adjacent charts with this provenance and an observed overlap point,
the seed is produced by a single finite gallery, not by replacing either chart
with the deterministic adjacent branch:

```lean
have adjacent_sector_seed_transport :
    forall {C1 C2 B1 B2}
      (hC1_open : IsOpen C1) (hC2_open : IsOpen C2)
      (hC1_ball : exists c r, 0 < r /\ C1 = Metric.ball c r)
      (hC2_ball : exists c r, 0 < r /\ C2 = Metric.ball c r)
      (hB1 : DifferentiableOn Complex B1 C1)
      (hB2 : DifferentiableOn Complex B2 C2)
      (hprov1 : Adj412ChartProv C1 B1)
      (hprov2 : Adj412ChartProv C2 B2)
      {z0 : Fin n -> Fin (d + 1) -> Complex},
      z0 in C1 -> z0 in C2 ->
        exists W, IsOpen W /\ z0 in W /\
          W <= C1 \cap C2 /\ Set.EqOn B1 B2 W := by
  intro C1 C2 B1 B2 hC1_open hC2_open hC1_ball hC2_ball
    hB1 hB2 hprov1 hprov2 z0 hz1 hz2

  -- Retarget both terminal charts to exact metric balls centered at z0.
  obtain <r1, hr1, hball1_sub> :=
    SCV.exists_metric_ball_subset_of_mem_open hC1_open hz1
  obtain <r2, hr2, hball2_sub> :=
    SCV.exists_metric_ball_subset_of_mem_open hC2_open hz2
  let C1z := Metric.ball z0 r1
  let C2z := Metric.ball z0 r2
  let B1z := B1
  let B2z := B2

  -- Build one finite comparison gallery:
  --   C1z, reverse hprov1.seed_gallery, OmegaSeed412,
  --   hprov2.seed_gallery, C2z.
  -- Consecutive seeds are either stored in the two provenance galleries or
  -- the obvious restrictions from C1/C2 to C1z/C2z.
  let Gcarrier := adjacent_comparison_gallery_carriers
    hprov1 hprov2 C1z C2z
  let Gbranch := adjacent_comparison_gallery_branches
    hprov1 hprov2 B1z B2z

  have hconsecutive :
      forall j : Fin galleryLen,
        exists Wj, IsOpen Wj /\ Wj.Nonempty /\
          Wj <= Gcarrier (Fin.castSucc j) \cap Gcarrier (Fin.succ j) /\
          Set.EqOn (Gbranch (Fin.castSucc j))
            (Gbranch (Fin.succ j)) Wj := by
    -- reverse provenance seeds for the first half,
    -- the common raw seed chart in the middle,
    -- forward provenance seeds for the second half,
    -- and metric-ball restriction seeds at the two endpoints
    exact adjacent_gallery_consecutive_seeds hprov1 hprov2

  have hpair_seed :
      forall i j, (Gcarrier i \cap Gcarrier j).Nonempty ->
        exists W, IsOpen W /\ W.Nonempty /\
          W <= Gcarrier i \cap Gcarrier j /\
          Set.EqOn (Gbranch i) (Gbranch j) W := by
    intro i j hij
    -- Use the local OS-I analytic-element uniqueness in the selected
    -- adjacent initial-sector overlap at an arbitrary point of the overlap.
    -- The uniqueness input is the raw seed `OmegaSeed412/BSeed412`, carried to
    -- both charts by their provenance galleries.  This is the genuine
    -- adjacent `(4.12)` branch-law step.
    exact adjacent_OSI45_analytic_element_uniqueness_seed
      H OmegaSeed412 BSeed412 Gcarrier Gbranch hconsecutive i j hij

  have hall :
      forall i j, Set.EqOn (Gbranch i) (Gbranch j)
        (Gcarrier i \cap Gcarrier j) :=
    SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds
      adjacent_gallery_metric_balls adjacent_gallery_holo hpair_seed

  -- Restrict the equality between the two retargeted endpoint charts to a
  -- smaller ball around z0.
  obtain <rho, hrho, hrho_sub> :=
    SCV.exists_metric_ball_subset_inter_of_mem_open
      Metric.isOpen_ball (Metric.mem_ball_self hr1)
      Metric.isOpen_ball (Metric.mem_ball_self hr2)
  refine <Metric.ball z0 rho, Metric.isOpen_ball,
    Metric.mem_ball_self hrho, ?_, ?_>
  · intro z hz
    exact <hball1_sub (hrho_sub hz).1, hball2_sub (hrho_sub hz).2>
  · intro z hz
    exact hall endpointLeft endpointRight z (hrho_sub hz)
```

Implementation note: `adjacent_OSI45_analytic_element_uniqueness_seed` marks a
live proof obligation, not an input to assume.  In the proof body it has to be
obtained by applying the OS-I identity theorem to the two analytic elements
whose domains are connected through the stored galleries and whose common
initial restriction is `OmegaSeed412/BSeed412`.  If it is split out, the split
must prove that exact analytic-element uniqueness statement.  A theorem that
takes the desired local overlap seed, pairwise equality, `Wadj`, or `Hdiff` as
an input is a wrapper and should be deleted rather than extended.

#### Adjacent seed shrink before the gallery

The raw `(4.12)` seed chart from
`H.OS412SeedWindow_metricBallChartInWindow OS lgc hxP` has carrier contained in

```lean
{z | BHW.permAct (d := d) P.τ z in BHW.ForwardTube d n} inter H.OmegaJ.
```

That raw window is the correct OS-I initial germ, but it is not by itself the
two-sheet overlap carrier needed for the Figure-2-4 gallery.  Before inserting
the seed chart into `Adj412ChartProv`, the proof must shrink the raw metric
ball using the checked point membership

```lean
H.OS412Seed_mem_initialSectorOverlap x hxP :
  BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) in
    BHW.ExtendedTube d n inter BHW.permutedExtendedTubeSector d n P.τ
```

and the openness of both sheets.  The resulting first gallery carrier is:

```lean
let zseed := BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))
let SeedOverlap :=
  rawSeedCarrier inter BHW.ExtendedTube d n inter
    BHW.permutedExtendedTubeSector d n P.τ

have hSeedOverlap_open : IsOpen SeedOverlap := by
  -- raw seed carrier is open, and both initial sheets are open

have hzseed_overlap : zseed in SeedOverlap := by
  exact <hzseed_raw, (H.OS412Seed_mem_initialSectorOverlap x hxP).1,
    (H.OS412Seed_mem_initialSectorOverlap x hxP).2>

obtain <rseed, hrseed, hseed_ball_sub> :=
  SCV.exists_metric_ball_subset_of_mem_open
    hSeedOverlap_open hzseed_overlap

let Cseed := Metric.ball zseed rseed
let Bseed := rawSeedBranch
```

Only `Cseed/Bseed`, not the unshrunk raw seed window, enters the adjacent
one-branch gallery.  Its fields are then:

```lean
have hCseed_sub :
    Cseed <= BHW.ExtendedTube d n inter
      BHW.permutedExtendedTubeSector d n P.τ inter H.OmegaJ := by
  intro z hz
  have hz' := hseed_ball_sub hz
  exact <hz'.2.1, hz'.2.2, hz'.1.2>

have hBseed_holo : DifferentiableOn Complex Bseed Cseed := by
  exact rawSeed_holo.mono (fun z hz => (hseed_ball_sub hz).1)

have hBseed_trace :
    Bseed zseed = bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  exact rawSeed_trace
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
    -- This is the exact OS-I `(4.14)` common-boundary theorem for the current
    -- ordinary `(4.1)` element and transported genuine adjacent `(4.12)`
    -- element.  It is assembled from the proof-local Figure-2-4
    -- OS-I §4.5 source boundary leaf and
    -- `SCV.distribution_representation_of_local_representations_for_test`.
    -- It is the only nonmechanical flat-transfer input.

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
    exact
      BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn
        (d := d) hd OS lgc (P := P) hUlocal_sub hsource_zero_rep

  have h414_common_boundary :
      exists T414 :
        SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex ->L[Complex] Complex,
        (forall phi, HasCompactSupport (phi :
            BHW.OS45FlatCommonChartReal d n -> Complex) ->
          tsupport (phi :
            BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
          (integral fun x =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun a => (x a : Complex)) * phi x) =
            T414 phi) /\
        (forall phi, HasCompactSupport (phi :
            BHW.OS45FlatCommonChartReal d n -> Complex) ->
          tsupport (phi :
            BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
          (integral fun x =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (fun a => (x a : Complex)) * phi x) =
            T414 phi) := by
    refine <Tlocal, h414_pairings_to_Tlocal.1, h414_pairings_to_Tlocal.2>

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
    exact
      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
        (d := d) hd OS lgc (P := P) Tlocal
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
        phi hphi_compact (hphiE.trans hE_sub)

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
    -- This is the flat `(4.14)` output of the proof-local OS-I
    -- common-boundary transfer, not a finite-side-height Schwinger identity
    -- and not a Wick/source normalization.
    obtain <T414, hOrd_T414, hAdj_T414> := h414_common_boundary
    exact (hAdj_T414 phi hphi_compact hphiE).trans
      (hOrd_T414 phi hphi_compact hphiE).symm

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
    exact (h414_integrals phi hphi_compact hphiE).trans
      (hzero_plus phi hphi_compact hphiE)

  exact <hE_open, hE_sub, Tlocal, hzero_plus, hzero_minus>
```

The flat block has no public theorem placeholder left.  The proof-local
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
  hsource_zero_rep, a local zero representation of the horizontal source
  pulled-branch difference Ghoriz on Ulocal.  The checked source-to-flat
  reducer then packages this as h414_common_boundary with T414 := Tlocal.
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
`hsource_zero_rep`.  It should not be exported as a public theorem surface
that assumes the hard transfers; it must be proved inside the Stage-A source
zero representation from the ordinary `(4.1)` endpoint, the raw transported
adjacent `(4.12)` chain, and `(4.14)` boundary covariance.

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

The remaining genuine mathematical work is exactly the two transfer
congruences below.  They are not assumptions for a public theorem.  They must
be proved from the ordinary `(4.1)` chain, the transported genuine adjacent
`(4.12)` chain, and their endpoint-centered trace formulas.

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
  -- Inline the ordinary `(4.1)/(4.14)` branch/source transfer.
  -- Build the eventual ordinary side pullback by the checked signed
  -- source-side normal form, prove the ordinary moving side-height
  -- boundary-value limit against the selected `(4.1)` boundary CLM, compare
  -- that limit with the checked source-side Schwinger limit, and lift the
  -- fixed-direction statement to the singleton `Keta`.
  -- The expanded Lean-pseudocode body is the "Exact Side-Height `(4.14)`
  -- Transfer Leaf" below; there is no theorem call to insert here.
  -- In Lean, paste that body here rather than calling a wrapper theorem.

have hMinus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  -- Inline the transported raw-adjacent `(4.12)/(4.14)` branch/source
  -- transfer.  Start from `OmegaSeed412/BSeed412`, transport that analytic
  -- element through the adjacent one-branch chain, rewrite to the terminal
  -- flat endpoint only after the chain supplies the overlap equality, then
  -- apply the same moving boundary-value calculation on the minus sheet.
  -- The deterministic `extendF o permAct` expression is endpoint
  -- bookkeeping here, never upstream seed data.
  -- In Lean, paste that body here rather than calling a wrapper theorem.
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
  -- proof-local source zero representation plus checked source-to-flat
  -- reducer; expanded below
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
`AdjEdge = OrdEdge`; in the Lean proof this is produced from the stronger
source-side zero representation `hsource_zero_rep` and the checked
source-to-flat reducer.  Individual zero-height normalization to the Wick or
Schwinger anchor is category-confused and circular when used as a primitive
shortcut; as a derived boundary-limit consequence it is just the expanded
proof of the common-boundary equality.

The active proof-local target is therefore:

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
  -- OS-I `(4.14)` source common-boundary theorem for the current ordinary
  -- `(4.1)` analytic element and transported genuine adjacent `(4.12)`
  -- analytic element.

have hpairings_to_Tlocal :=
  BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn
    (d := d) hd OS lgc (P := P) hUlocal_sub hsource_zero_rep
```

The compact-test equality is then just:

```lean
have h414_integrals_phi : AdjEdge = OrdEdge := by
  exact (hpairings_to_Tlocal.2 phi hphi_compact hphiE).trans
    (hpairings_to_Tlocal.1 phi hphi_compact hphiE).symm
```

The checked common-edge change-of-variables lemmas remain useful only as
coordinate bookkeeping after the source-side zero representation has been
proved:
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
for `hsource_zero_rep`.

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
boundary-value theorem.  The `TendstoUniformlyOn ... Keta` target below is
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
    (tendstoUniformlyOn_singleton_iff_tendsto
      (F := fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
      (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (p := nhdsWithin (0 : Real) (Set.Ioi 0))
      (x := eta0)).2 hPlus_asymptotic_eta0
```

and similarly for the adjacent/minus side.  This uses Mathlib's
`tendstoUniformlyOn_singleton_iff_tendsto` directly; do not add a local
singleton wrapper.

The fixed-direction boundary-value theorem itself has two layers:

1. a pure SCV moving-test boundary-value lemma, proved from raywise fixed-test
   boundary convergence, the uniform seminorm bound for the slice integral
   CLMs near `eps = 0`, and Schwartz convergence of the moving tests;
2. an OS-I normalization step which identifies the resulting boundary
   functional with the Figure-2-4 Schwinger/source pairing for the current
   ordinary `(4.1)` analytic element or transported genuine adjacent `(4.12)`
   analytic element.

Layer 1 only lands in the selected boundary functional (`bvt_W` or the
corresponding local analytic-element boundary functional).  It does **not**
by itself prove equality with `OS.S`, and using it alone as
`h414_integrals` would be the same circular shortcut rejected above.  Layer 2
is the real OS-I `(4.1)/(4.12)/(4.14)` content.

The neutral core of Layer 1 is now checked in production Lean as
`SCV.tube_boundaryValueData_moving_of_fixed` in
`OSReconstruction/SCV/TubeBoundaryValues.lean`.  Do not add a new OS45-facing
wrapper for it.  When the branch is literally a tube-domain boundary value,
apply this theorem to the already-selected boundary functional (`bvt_W` for
the ordinary `(4.1)` endpoint, or the transported adjacent boundary CLM for the
raw `(4.12)` endpoint).  It exposes the private positive-height slice CLMs and
uses `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter` internally.

For non-tube local chart reductions, the same ambient rule is still the
Lean-facing fallback: use `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`
on the **ambient** `SchwartzNPoint d n` space, after restricting the
complex-linear slice CLMs and the boundary CLM to real scalars.  The side tests
live in the subtype `ZeroDiagonalSchwartz d n`, so first compose their
convergence with `Subtype.val`; do not try to apply the Schwartz theorem
directly to the subtype:

```lean
-- inside the fixed-direction branch-side proof
let l := nhdsWithin (0 : Real) (Set.Ioi 0)
let Treal :
    Real -> SchwartzNPoint d n ->L[Real] Complex :=
  fun eps => (T eps).restrictScalars Real
let Wreal : SchwartzNPoint d n ->L[Real] Complex :=
  W.restrictScalars Real

have hfixed_real :
    forall psi : SchwartzNPoint d n,
      Tendsto (fun eps => Treal eps psi) l (nhds (Wreal psi)) := by
  intro psi
  simpa [Treal, Wreal] using hfixed psi

have hmove_val :
    Tendsto (fun eps => ((psieps eps).1 : SchwartzNPoint d n))
      l (nhds ((psi0).1 : SchwartzNPoint d n)) := by
  exact (continuous_subtype_val.tendsto psi0).comp hmove

have hmoving_to_W :
    Tendsto (fun eps => T eps ((psieps eps).1 : SchwartzNPoint d n))
      l (nhds (W ((psi0).1 : SchwartzNPoint d n))) := by
  have h :=
    SchwartzMap.tempered_apply_tendsto_of_tendsto_filter
      (T := Treal) (S := Wreal) hfixed_real hmove_val
  simpa [Treal, Wreal] using h
```

For the tube-domain boundary-value theorem, `SCV.tube_boundaryValueData_moving_of_fixed`
has the Lean shape:

```lean
have hmoving_to_W :
    Tendsto
      (fun eps : Real =>
        integral fun x : Fin n -> Fin (d + 1) -> Real =>
          F (fun k mu => (x k mu : Complex) +
            (eps : Complex) * (eta0 k mu : Complex) * Complex.I) *
            phieps eps x)
      l (nhds (W phi0)) := by
  exact
    SCV.tube_boundaryValueData_moving_of_fixed
      (C := C) hC_cone hF_hol C_bd N hC_pos hF_growth
      W hW_fixed eta0 heta0
      (fun eps : Real => eps) h_eps_to_edge
      hphieps_to_phi0
```

Here `W` is the selected ambient boundary functional and `hW_fixed` is the
fixed-test boundary-value convergence for every `SchwartzNPoint d n` test.
The theorem packages the Banach-Steinhaus/equicontinuity argument; it does not
identify `W phi0` with any Schwinger value.  The subsequent OS-I work is the
branch/source asymptotic comparison: the branch-side side-height integrals and
the source-side Wick-section integrals must have difference tending to zero.
The checked source-side Schwinger limit then supplies the common limit.

The fixed-direction branch proof should therefore be transcribed with the
following dependency order.  The first and third bullets are checked support;
the middle bullet is the genuine OS-I mathematical gap.

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

-- checked support: fixed-test boundary values give the selected boundary
-- functional for the ordinary or transported adjacent branch.  Keep the
-- all-direction theorem for the SCV moving-test call, then specialize it to
-- the chosen flat direction only for local rewrites.
have hWord_fixed :
    forall (psi : SchwartzNPoint d n)
      (eta : Fin n -> Fin (d + 1) -> Real),
      eta ∈ ordinary41_forwardCone ->
      Tendsto
        (fun eps : Real =>
          ordinary41_tubeIntegral eps eta psi)
        l (nhds (Word psi)) := by
  intro psi eta heta
  -- Ordinary sector:
  -- 1. restrict the endpoint-centered ordinary chart to the tube ray
  --    `x + i eps eta`;
  -- 2. rewrite the branch by `hOrd_terminal_eq_extendF`;
  -- 3. apply the checked ordinary OS-I `(4.1)` boundary-value theorem
  --    (`bvt_boundary_values`, or `bvt_boundary_values_moving` with a
  --    constant test);
  -- 4. rewrite the selected boundary CLM as `Word`, the ordinary terminal
  --    boundary functional carried by the one-branch chain.
  have hray_rewrite :
      ∀ᶠ eps in l,
        ordinary41_tubeIntegral eps eta psi =
          integral fun x : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (fun k mu =>
                (x k mu : Complex) +
                  (eps : Complex) * (eta k mu : Complex) * Complex.I) *
            psi x := by
    filter_upwards [ordinary41_endpoint_ray_in_carrier_eventually
      endpointOrd eta heta psi] with eps heps
    exact integral_congr_ae (heps hOrd_terminal_eq_extendF)
  have hbvt :
      Tendsto
        (fun eps : Real =>
          integral fun x : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (fun k mu =>
                (x k mu : Complex) +
                  (eps : Complex) * (eta k mu : Complex) * Complex.I) *
            psi x)
        l (nhds (bvt_W OS lgc n psi)) := by
    exact bvt_boundary_values (d := d) OS lgc n psi eta heta
  have hWord_norm : Word psi = bvt_W OS lgc n psi := by
    exact chainOrd.terminal_boundaryCLM_eq_bvt_W psi
  exact hbvt.congr' hray_rewrite.symm |>.congr (by simpa [hWord_norm])

have hfixedOrd :
    forall psi : SchwartzNPoint d n,
      Tendsto (fun eps => Tord eps psi) l (nhds (Word psi)) := by
  intro psi
  exact (hWord_fixed psi eta0 heta0).congr' Tord_eq_ordinary41_tubeIntegral

have hWadj_fixed :
    forall (psi : SchwartzNPoint d n)
      (eta : Fin n -> Fin (d + 1) -> Real),
      eta ∈ adjacent412_forwardCone ->
      Tendsto
        (fun eps : Real =>
          adjacent412_tubeIntegral eps eta psi)
        l (nhds (Wadj psi)) := by
  intro psi eta heta
  -- Adjacent sector:
  -- 1. work with the analytic element transported from
  --    `OmegaSeed412/BSeed412`, not with the deterministic endpoint branch;
  -- 2. on the raw seed chart rewrite
  --    `BSeed412 z = bvt_F OS lgc n (BHW.permAct P.τ z)`;
  -- 3. after applying `permAct P.τ` to the tube ray, reduce the fixed-test
  --    boundary value to the checked ordinary boundary-value theorem for
  --    `bvt_F`, with the permuted test and permuted forward-cone direction;
  -- 4. use the finite adjacent one-branch chain to transport the resulting
  --    boundary CLM to the terminal `Wadj`; the endpoint equality
  --    `hAdj_terminal_eq_endpoint` is used only in this last rewrite.
  let etaτ : Fin n -> Fin (d + 1) -> Real :=
    fun k mu => eta (P.τ k) mu
  have heta_perm : etaτ ∈ ForwardConeAbs d n := by
    -- Unfold `adjacent412_forwardCone`: it is the preimage, under the real
    -- permutation action on labels, of the ordinary forward cone.  This is
    -- local cone bookkeeping, not an OS analytic input.
    simpa [adjacent412_forwardCone, etaτ]
      using heta
  let psiτ : SchwartzNPoint d n :=
    BHW.permuteSchwartz (d := d) P.τ.symm psi
  have hraw_fixed :
      Tendsto
        (fun eps : Real =>
          integral fun x : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (fun k mu =>
                (x k mu : Complex) +
                  (eps : Complex) *
                    (etaτ k mu : Complex) *
                    Complex.I) *
            psiτ x)
        l (nhds (bvt_W OS lgc n psiτ)) := by
    exact bvt_boundary_values (d := d) OS lgc n psiτ etaτ heta_perm
  have hraw_to_adj :
      ∀ᶠ eps in l,
        adjacent412_tubeIntegral eps eta psi =
          integral fun x : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (fun k mu =>
                (x k mu : Complex) +
                  (eps : Complex) *
                    (etaτ k mu : Complex) *
                    Complex.I) *
            psiτ x := by
    filter_upwards [chainAdj.raw412_ray_rewrite_eventually
      OmegaSeed412 BSeed412 endpointAdj hAdj_terminal_eq_endpoint eta heta psi]
      with eps heps
    exact integral_congr_ae heps
  have hWadj_norm : Wadj psi = bvt_W OS lgc n psiτ := by
    exact chainAdj.terminal_boundaryCLM_eq_raw412_bvt_W
      OmegaSeed412 BSeed412 endpointAdj hAdj_terminal_eq_endpoint psi
  exact hraw_fixed.congr' hraw_to_adj.symm |>.congr (by simpa [hWadj_norm])

have hfixedAdj :
    forall psi : SchwartzNPoint d n,
      Tendsto (fun eps => Tadj eps psi) l (nhds (Wadj psi)) := by
  intro psi
  exact (hWadj_fixed psi eta0 heta0).congr' Tadj_eq_adjacent412_tubeIntegral

-- checked support: move from fixed tests to the side-cutoff tests.
have hOrd_moving :
    Tendsto
      (fun eps => Tord eps ((psiepsPlus eps).1 : SchwartzNPoint d n)) l
      (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
  -- In the ordinary selected OS endpoint chart this is the checked theorem
  -- `bvt_boundary_values_moving`, followed by the local rewrite from the
  -- ordinary endpoint branch to `bvt_F`.
  exact
    (bvt_boundary_values_moving
      (d := d) OS lgc n eta0 heta0
      (fun eps : Real => eps) h_eps_to_edge hpsiPlus_move_val).congr'
      Tord_eq_bvtF_endpoint_eventually

have hAdj_moving :
    Tendsto
      (fun eps => Tadj eps ((psiepsMinus eps).1 : SchwartzNPoint d n)) l
      (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
  -- The adjacent branch is not the selected `bvt_W` witness until the raw
  -- `(4.12)` element has been transported.  Use the pure SCV theorem with
  -- the transported adjacent boundary CLM, not `bvt_boundary_values_moving`
  -- against the downstream deterministic branch.
  exact
    SCV.tube_boundaryValueData_moving_of_fixed
      (C := adjacent412_forwardCone)
      adjacent412_forwardCone_isCone
      adjacent412_endpoint_holomorphic C_bd N hC_bd_pos adjacent412_growth
      Wadj hWadj_fixed eta0 heta0
      (fun eps : Real => eps) h_eps_to_edge
      hpsiMinus_move_val

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
`TendstoUniformlyOn ... Keta`, and apply
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
  --   chainOrd : one_branch_chain_witness ordinary41
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
    -- Inline body, no exported theorem:
    -- * use the checked signed side pullback to rewrite `BranchPlusSide`
    --   eventually as
    --     `Jflat * ∫ u, extendF(bvt_F)(sourceSide 1 eps eta0 u)
    --        * (psiPlus eps eta0).1 u`;
    -- * use `os45FlatCommonChart_sourceSide_mem_extendedTube_eventually` to
    --   place the source-side arguments in the ordinary outgoing sheet;
    -- * apply the ordinary `(4.1)` fixed-test boundary value and the checked
    --   moving-test upgrade to the family `psiPlus eps eta0`;
    -- * use `(4.14)` covariance/source normalization to identify the selected
    --   boundary value with
    --     `Jflat * OS.S n (D.toZeroDiagonalCLM 1 phi)`;
    -- * subtract the checked source-side limit for `SourcePlusSide`.
    have hBranchPlus_to_common :
        Tendsto (fun eps => BranchPlusSide eps eta0)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds
            (Jflat *
              OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) phi))) := by
      -- This is the ordinary OS-I leaf just described, assembled in this
      -- proof body from the checked coordinate/support/moving-test lemmas.
      -- The proof term is the local chain of `have`s in the exact
      -- side-height transfer leaf: pullback, sheet membership, ordinary
      -- fixed-test boundary value, moving-test upgrade, and source
      -- normalization.
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
      (tendstoUniformlyOn_singleton_iff_tendsto
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
  --   chainAdj : one_branch_chain_witness adjacent412
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
      -- Inline body, no exported theorem:
      -- * use the checked signed side pullback on the minus sheet;
      -- * use the source-side sheet-membership packet for
      --   `P.τ.symm * 1`;
      -- * keep the raw `OmegaSeed412/BSeed412` provenance through the
      --   adjacent one-branch chain;
      -- * apply `(4.12)` fixed-test boundary values after the appropriate
      --   permutation of the tube ray;
      -- * use the pure moving-test upgrade on `psiMinus eps eta0`;
      -- * only then rewrite the terminal endpoint by
      --   `hAdj_terminal_eq_endpoint` and identify the same source common
      --   limit `Jflat * OS.S n (D.toZeroDiagonalCLM 1 phi)`.
      -- The proof term is the local chain of `have`s in the exact
      -- side-height transfer leaf: minus pullback, raw-seed transport,
      -- adjacent fixed-test boundary value, moving-test upgrade, and source
      -- normalization.
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
      (tendstoUniformlyOn_singleton_iff_tendsto
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
-- already `OS.S n (...)`, then feed that as `h414_integrals`.
```

The missing OS-I content is precisely the local normalization that compares the
ordinary `(4.1)` and transported adjacent `(4.12)` branch-side boundary traces
with the checked source-side Schwinger limits on the cutoff-pulled tests.  A
valid proof may use `bvt_boundary_values` as one analytic ingredient, but only
after it supplies the OS-I identity-theorem/edge-transfer step that connects
the resulting `bvt_W` boundary value to the Schwinger-side source pairing in
this Figure-2-4 window.

The moving-test part of that analytic ingredient is checked as
`SCV.tube_boundaryValueData_moving_of_fixed`.  Use it only after the boundary
functional has already been selected.  For the ordinary selected OS witness,
the specialized theorem is now checked as `bvt_boundary_values_moving`, so the
ordinary side can be written directly as:

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
              (eps : Complex) * (eta0 k mu : Complex) * Complex.I) *
          (((psiepsPlus eps eta0).1 : SchwartzNPoint d n) x))
      l (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
  exact
    bvt_boundary_values_moving
      (d := d) OS lgc n eta0 heta0
      (fun eps : Real => eps) h_eps_to_edge
      hpsiPlus_move_val
```

This pseudo-code names local proof facts, not new public theorem surfaces.  The
adjacent side uses the same theorem only after the raw `(4.12)` analytic
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

This means the remaining proof does not have to re-establish source-window
support for moving tests.  It still must prove the actual boundary-value
convergence of the ordinary and transported adjacent analytic elements on
those tests.

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
  -- 2. Subdivide each checked JoinedIn corridor by
  --    UnitIntervalSubdivision and local metric balls inside the open
  --    two-sheet overlap.
  -- 3. Attach ordinary or adjacent local transfer provenance to each
  --    successor ball.
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
  terminalBranch = B (Fin.last m)
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

## Local Transfer Cases

The finite chain is built from a proof-local transfer theorem along the
Figure-2-4 path.  For a step from `p = gamma s0` to `q = gamma s1`, first
restrict the current chart to a metric ball inside the incoming sheet and the
selected chart window.  Then produce the successor chart and a nonempty
complex-open transition seed.

The transfer has exactly three cases.

The checked carrier fields used by these cases are now fixed:

| Case | Incoming/outgoing domain | Checked data already available | Still mathematical |
| --- | --- | --- | --- |
| Ordinary sector | `BHW.ExtendedTube d n` | `H.ordinaryWick_metricBallChartInWindow`, `H.ordinaryCommonEdge_metricBallChartInWindow`, `BHW.os45Figure24Path_endpoint_extendF_eq_ordinaryPulledRealBranch`, ordinary `extendF` holomorphy and invariance | only metric-ball shrinking and identity-theorem propagation |
| Adjacent sector | `BHW.permutedExtendedTubeSector d n P.τ` | raw `(4.12)` seed window `H.OS412SeedWindow_metricBallChartInWindow`, seed obstruction `H.ordinaryWick_not_mem_OS412SeedWindow`, corridor geometry `BHW.os45Figure24_joined_adjacentWick_to_adjLift0_initialSectorOverlap`, `BHW.os45Figure24_joined_adjLift0_to_adjLift1_initialSectorOverlap`, `BHW.os45Figure24_joined_adjLift_to_permActIdentityPath_initialSectorOverlap`, `BHW.os45Figure24_joined_permActOrdinaryWick_to_permActCommonEdge_initialSectorOverlap`, and endpoint bookkeeping `H.adjacentCommonEdge_metricBallChartInWindow` | the branch-law equality that transports the genuine `(4.12)` analytic element; this is not `extendF o permAct` as an initial seed |
| Flat real-Jost, upstream inside `hadj412` | plus side `BHW.os45FlatCommonChartOmega d n 1`, minus side `BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)`, edge `os45CommonEdgeFlatCLE d n 1 '' Ulocal` | edge-window support, checked ordinary-edge representation, endpoint chart bookkeeping, and `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM` after the two zero-height pairings are proved | `hsource_zero_rep`: the OS-I `(4.14)` source zero representation for the current ordinary `(4.1)` and transported adjacent `(4.12)` elements |
| Flat real-Jost, downstream after `h45_source_eqOn` | same flat chart domains | `BHW.os45FlatCommonChart_zeroHeight_pairings_eq_of_sourceCommonEdge_eqOn` and `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn` | the proof-local source common-edge equality `h45_source_eqOn`, produced only after `Badj412` has Wick and common-edge traces |

Thus the flat case has two layers.  The upstream layer is the only place where
the genuine adjacent `(4.12)` analytic element crosses the horizontal
common-edge side while `hadj412` is still being built.  The downstream checked
bridge consumes `h45_source_eqOn` and returns an ambient EOW seed after the
Wick-seed identity theorem has already produced that equality.  The upstream
transfer cannot call the downstream bridge with `h45_source_eqOn` as a
hypothesis and then claim the transfer is done.

Each case must instantiate the same proof-local return shape:

```lean
have local_transfer_step :
    forall
      (kind : BranchKind)
      (p q : Fin n -> Fin (d + 1) -> Complex)
      (Cprev : Set (Fin n -> Fin (d + 1) -> Complex))
      (Bprev : (Fin n -> Fin (d + 1) -> Complex) -> Complex),
      p in Cprev ->
      IsOpen Cprev ->
      (exists rprev : Real, 0 < rprev /\ Cprev = Metric.ball p rprev) ->
      Cprev <= sheet kind ->
      DifferentiableOn Complex Bprev Cprev ->
      -- retained proof-local provenance saying Bprev is the current
      -- continuation of the selected initial germ
      current_chain_provenance kind Bprev Cprev ->
      transfer_case kind p q ->
        exists (Cnext : Set (Fin n -> Fin (d + 1) -> Complex))
          (Bnext : (Fin n -> Fin (d + 1) -> Complex) -> Complex)
          (rnext : Real)
          (Wstep : Set (Fin n -> Fin (d + 1) -> Complex)),
          0 < rnext /\
          Cnext = Metric.ball q rnext /\
          q in Cnext /\
          Cnext <= sheet kind /\
          DifferentiableOn Complex Bnext Cnext /\
          IsOpen Wstep /\
          Wstep.Nonempty /\
          Wstep <= Cprev inter Cnext /\
          Set.EqOn Bprev Bnext Wstep /\
          next_chain_provenance kind Bnext Cnext := by
  -- implemented inline by the three cases below
```

`current_chain_provenance` and `next_chain_provenance` are proof-local
abbreviations or local `have` bundles.  They must not become public records.
Their only role is to remember whether the branch came from the ordinary
`(4.1)` seed or from the transported adjacent `(4.12)` seed, so that overlap
seeds can be proved later.

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
    Cprev_open hpCprev Cnext_open hqCnext

let Wstep := Metric.ball p rho
have hstep_eq : Set.EqOn Bprev Bnext Wstep := by
  intro z hz
  exact (hprev_global (hrho_sub hz).1).trans
    (hnext_global (hrho_sub hz).2).symm
```

### Adjacent-Sector Transfer

Incoming and outgoing sheet:

```text
AdjSheet = BHW.permutedExtendedTubeSector d n P.τ
```

The initial chart is the genuine `OmegaAdj0` / `BAdj0` chart above.  A transfer
step in this sector propagates that corrected section 4.12 element.  It must
not replace the initial chart by the deterministic downstream branch using
`extendF` after the permutation action.

The critical non-shortcut is now explicit.  The checked theorem
`BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3` is the right identity-theorem
engine, but in the upstream proof its adjacent input must be the transported
genuine `(4.12)` analytic element:

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
Gemini `gemini-3.1-pro-preview` audit on 2026-05-16 confirmed this shortcut is
unsound for the strict route: it assumes the raw adjacent analytic continuation
is already the downstream deterministic permuted continuation.  The corrected
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
have hprev_seed :
    exists Wseed, IsOpen Wseed /\ Wseed.Nonempty /\
      Wseed <= Cprev inter OmegaAdj0 /\
      Set.EqOn Bprev BAdj0 Wseed := by
  -- from adjacent412 provenance

-- Build Cnext by the local BHW/OS-I chart around q inside AdjSheet.
-- Its branch Bnext is the same analytic element continued from BAdj0,
-- not the deterministic `extendF o permAct` branch.

have hnext_seed :
    exists Wseed, IsOpen Wseed /\ Wseed.Nonempty /\
      Wseed <= Cnext inter OmegaAdj0 /\
      Set.EqOn Bnext BAdj0 Wseed := by
  -- one adjacent-sector transfer step from retained provenance

have hstep_eq :
    exists Wstep, IsOpen Wstep /\ Wstep.Nonempty /\
      Wstep <= Cprev inter Cnext /\
      Set.EqOn Bprev Bnext Wstep := by
  -- connect both local representatives to BAdj0 by the local identity theorem
  -- on a metric-ball shrink inside their common adjacent-sector chart
```

The last line is where the adjacent-sector Hall-Wightman branch law is used.
It is still a genuine mathematical subproof, not topology and not an existing
deterministic formula.

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
2. Prove the OS-I `(4.14)` local source zero representation
   `hsource_zero_rep` for the horizontal pulled-branch difference `Ghoriz` on
   `Ulocal`.  This is the genuine mathematical step.
3. Feed `hsource_zero_rep` to the checked source-to-flat reducer
   `BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn`.
   It produces both zero-height compact-test pairings against the already
   checked ordinary CLM `Tlocal`.
4. Package those two fields as `h414_common_boundary` by choosing
   `T414 := Tlocal`; then derive
   `∫ Fminus0 * phi = ∫ Fplus0 * phi` by transitivity.
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
  -- Exact OS-I `(4.14)` local source common-boundary theorem for the current
  -- ordinary `(4.1)` and transported genuine adjacent `(4.12)` analytic
  -- elements.  It is assembled from the proof-local Figure-2-4 difference
  -- germ and `SCV.distribution_representation_of_local_representations_for_test`.

have h414_pairings_to_Tlocal :
    (forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
      HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
      tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fplus0 x * phi x) = Tlocal phi) /\
    (forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
      HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
      tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fminus0 x * phi x) = Tlocal phi) := by
  exact
    BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn
      (d := d) hd OS lgc (P := P) hUlocal_sub hsource_zero_rep

have h414_common_boundary :
    exists T414 :
      SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex ->L[Complex] Complex,
      (forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
        HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x : BHW.OS45FlatCommonChartReal d n =>
          Fplus0 x * phi x) = T414 phi) /\
      (forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
        HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x : BHW.OS45FlatCommonChartReal d n =>
          Fminus0 x * phi x) = T414 phi) := by
  exact <Tlocal, h414_pairings_to_Tlocal.1, h414_pairings_to_Tlocal.2>

have h414_integrals :
    forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
      HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
      tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fminus0 x * phi x) =
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fplus0 x * phi x) := by
  obtain <T414, hOrd_T414, hAdj_T414> := h414_common_boundary
  intro phi hphi_compact hphiE
  exact (hAdj_T414 phi hphi_compact hphiE).trans
    (hOrd_T414 phi hphi_compact hphiE).symm

have hzero_plus :
    forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
      HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
      tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fplus0 x * phi x) =
        Tlocal phi := by
  -- checked ordinary-edge representation, restricted from the full edge to E

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

### Source Zero Representation Leaf

The flat crossing is Lean-ready only when the proof of `hsource_zero_rep` is
spelled out as a proof body, not as a new public hypothesis.  The exact
source-side target is:

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
      -- Genuine OS-I `(4.14)` local transfer:
      --   incoming sheet: ordinary `(4.1)` element on
      --     `BHW.ExtendedTube d n ∩ H.ΩJ`;
      --   outgoing sheet: transported genuine adjacent `(4.12)` element on
      --     `BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ`;
      --   side-height traces: endpoint-centered ordinary and adjacent
      --     common-edge charts, rewritten by the checked pulled-real endpoint
      --     lemmas and compared to source pairings by `(4.14)`.
      -- It returns the source pairing zero for `Ghoriz` on `V`.  This is the
      -- remaining nonmechanical OS-I leaf; it must be proved from the
      -- retained raw `(4.12)` chain provenance and the Figure-2-4 branch laws,
      -- not assumed as `h414_common_boundary`, `Wadj`, or `Hdiff`.
      have hhorizontal_zero :
          integral (fun u : NPointDomain d n => Ghoriz u * chi u) = 0 := by
        -- Direct OS-I `(4.14)` boundary-transfer body.  This is not an
        -- `Hdiff`/EOW argument and not a finite-height Wick-test transform.
        -- It proves the zero-height horizontal source pairing by:
        --   * pulling `chi` to a flat common-edge test with the explicit
        --     `os45CommonEdgeFlatCLE` Jacobian;
        --   * proving the ordinary and transported-adjacent branch-side
        --     side-height pairings have the same source-side Schwinger limit;
        --   * using `SCV.eq_zeroHeight_of_common_sideLimit` to get the
        --     zero-height flat common-boundary equality;
        --   * changing variables back to the source integral.
        -- No production helper call belongs here until the two OS-I transfer
        -- bodies above are proved.  Inline the ordinary and raw-adjacent
        -- branch/source asymptotic transfers, then inline the checked
        -- source-to-flat and side-limit algebra.

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
   `hMinus_asymptotic`.  These are the live mathematical gap.  They compare
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
side-height calculation.  This is the point where the previous transcript was
still too schematic.

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
  filter_upwards [hSideSupport] with eps heps_pos heps_support
  have hphiE_plus :
      tsupport (SCV.translateSchwartz (((1 : Real) * eps) • eta0) phi :
        BHW.OS45FlatCommonChartReal d n -> Complex) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P (1 : Equiv.Perm (Fin n)) :=
    heps_support.plus_edge
  exact
    BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM
      (d := d) (n := n) OS lgc D
      (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
      (1 : Real) eps eta0 phi hphiE_plus
      hBranchPlus_integrable_shifted
```

Here `hSideSupport` is the eventual positive-height packet supplied by the
checked side-support radius/cutoff lemmas, and
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
  -- The moving-test part is the checked `tube_boundaryValueData_moving_of_fixed`
  -- / `bvt_boundary_values_moving` layer after the ordinary local boundary
  -- CLM has been identified.  The final equality with `OS.S` is the checked
  -- source restriction theorem for zero-diagonal tests, applied to
  -- `D.toZeroDiagonalCLM 1 phi`.
  -- The Lean body is the local `have` sequence above; do not replace it by a
  -- public theorem that assumes this limit.
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
  filter_upwards [hSideSupport] with eps heps_pos heps_support
  have hphiE_minus :
      tsupport (SCV.translateSchwartz (((-1 : Real) * eps) • eta0) phi :
        BHW.OS45FlatCommonChartReal d n -> Complex) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P (1 : Equiv.Perm (Fin n)) :=
    heps_support.minus_edge
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
  -- The Lean body is the local `have` sequence above; do not replace it by a
  -- public theorem that assumes this limit.

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
`hsource_zero_rep`, `h414_common_boundary`, `Hdiff`, `Wadj`, a finite
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

The zero-height side-continuity inputs are already checked:

```lean
have hBranchPlus_zero :
    TendstoUniformlyOn
      BranchPlusSide
      (fun _ : BHW.OS45FlatCommonChartReal d n => OrdEdge)
      l Keta := by
  exact
    BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM
      (d := d) hd OS lgc
      (0 : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex ->L[Complex] Complex)
      Keta hKeta hKetaC phi hphi_compact hphiE
      (by simpa [OrdEdge])

have hBranchMinus_zero :
    TendstoUniformlyOn
      BranchMinusSide
      (fun _ : BHW.OS45FlatCommonChartReal d n => AdjEdge)
      l Keta := by
  exact
    BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_minus_of_zeroHeight_pairingCLM
      (d := d) hd OS lgc
      (0 : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex ->L[Complex] Complex)
      Keta hKeta hKetaC phi hphi_compact hphiE
      (by simpa [AdjEdge])
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

Do not try to prove a new compact-direction boundary-value theorem at this
stage.  The uniform-on-`Keta` statements are obtained from fixed-direction
`Tendsto` statements by `tendstoUniformlyOn_singleton_iff_tendsto`.

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
    have hsupport :=
      D.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually
        hUlocal_open Keta hKeta phi hphi_compact hphiUlocal
    filter_upwards [hinteg, hsupport] with eps hinteg_eps hsupport_eps
    exact
      BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
        (d := d) hd OS lgc D
        (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
        (1 : Real) eps eta0 phi
        (hsupport_eps eta0 hKeta_eta0).plus_edge
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

    have hOrd_branch_to_endpoint :
        ∀ᶠ eps in l,
          ∀ᵐ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (sourceSide (1 : Real) eps eta0 u) =
            chainOrd.terminalBranch
              (sourceSide (1 : Real) eps eta0 u) := by
      -- Use `hOrd_sheet`, the endpoint-centered ordinary terminal carrier,
      -- and the checked one-branch-chain equality
      -- `chainOrd.terminal_eq_ordinary_global`.  The outgoing flat side is
      -- `BHW.os45FlatCommonChartOmega d n 1`; the incoming source-side sheet
      -- is `BHW.ExtendedTube d n`.

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
      filter_upwards [hOrd_branch_to_endpoint] with eps heps
      exact integral_congr_ae (heps.mono
        (by intro u hu; rw [hu]))

    have hOrd_fixed :
        forall psi : SchwartzNPoint d n,
          Tendsto
            (fun eps =>
              integral fun u : NPointDomain d n =>
                chainOrd.terminalBranch
                  (sourceSide (1 : Real) eps eta0 u) * psi u)
            l (nhds (Word psi)) := by
      intro psi
      -- This is the ordinary `(4.1)` fixed-test boundary value on the
      -- endpoint-centered source-side ray.  In the literal tube coordinates
      -- it is `bvt_boundary_values`; in the retained local chart it is first
      -- transported through `chainOrd` by the same identity-theorem equality
      -- used in `hOrd_branch_to_endpoint`.

    have hOrd_moving :
        Tendsto
          (fun eps =>
            integral fun u : NPointDomain d n =>
              chainOrd.terminalBranch
                (sourceSide (1 : Real) eps eta0 u) *
              ((((psiPlus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          l (nhds (Word ((psi0).1 : SchwartzNPoint d n))) := by
      -- Apply `SCV.tube_boundaryValueData_moving_of_fixed` (or the checked
      -- specialization `bvt_boundary_values_moving` in the literal ordinary
      -- tube chart) to `hOrd_fixed` and `hpsiPlus_move`.

    have hOrd_source_norm :
        Word ((psi0).1 : SchwartzNPoint d n) =
          OS.S n (D.toZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) phi) := by
      -- OS-I `(4.14)` source normalization for the ordinary branch.  The
      -- endpoint value is the Wick/source section
      -- `u ↦ bvt_F OS lgc n (fun k => wickRotatePoint (u k))`; finish with
      -- `bvt_euclidean_restriction OS lgc n psi0`.

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
    (tendstoUniformlyOn_singleton_iff_tendsto
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
    have hsupport :=
      D.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually
        hUlocal_open Keta hKeta phi hphi_compact hphiUlocal
    filter_upwards [hinteg, hsupport, hAdj_terminal_eq_endpoint_eventually]
      with eps hinteg_eps hsupport_eps hterminal_eps
    have hraw_pullback :=
      BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
        (d := d) hd OS lgc D
        (P.τ.symm * (1 : Equiv.Perm (Fin n))) (1 : Equiv.Perm (Fin n))
        (-1 : Real) eps eta0 phi
        (hsupport_eps eta0 hKeta_eta0).minus_edge
        (hinteg_eps eta0 hKeta_eta0).2
    -- `hterminal_eps` rewrites the `extendF (bvt_F) (permAct P.τ ...)`
    -- expression in `hraw_pullback` to `Badj_terminal (...)`.
    exact hraw_pullback.trans (integral_congr_ae (hterminal_eps eta0 hKeta_eta0))

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

    have hAdj_raw_endpoint :
        ∀ᶠ eps in l,
          ∀ᵐ u : NPointDomain d n,
            Badj_terminal (sourceSide (-1 : Real) eps eta0 u) =
            chainAdj.terminalBranch
              (sourceSide (-1 : Real) eps eta0 u) := by
      -- The adjacent incoming sheet is the raw `(4.12)` window
      -- `{z | BHW.permAct P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ` with branch
      -- `BSeed412 z = bvt_F OS lgc n (BHW.permAct P.τ z)`.  The outgoing
      -- flat side is `BHW.os45FlatCommonChartOmega d n (P.τ.symm * 1)`.
      -- Use the retained adjacent one-branch chain to reach the terminal
      -- endpoint, then use the endpoint equality only on this terminal
      -- chart.

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
      filter_upwards [hAdj_raw_endpoint] with eps heps
      exact integral_congr_ae (heps.mono
        (by intro u hu; rw [hu]))

    have hAdj_fixed :
        forall psi : SchwartzNPoint d n,
          Tendsto
            (fun eps =>
              integral fun u : NPointDomain d n =>
                chainAdj.terminalBranch
                  (sourceSide (-1 : Real) eps eta0 u) * psi u)
            l (nhds (Wadj psi)) := by
      intro psi
      -- Apply OS-I `(4.12)` to the raw seed: first rewrite on
      -- `OmegaSeed412/BSeed412`, then apply the label permutation to the
      -- tube ray and to the test.  The fixed-test boundary value is
      -- transported to the terminal CLM through the retained adjacent chain.

    have hAdj_moving :
        Tendsto
          (fun eps =>
            integral fun u : NPointDomain d n =>
              chainAdj.terminalBranch
                (sourceSide (-1 : Real) eps eta0 u) *
              ((((psiMinus eps eta0).1 : SchwartzNPoint d n) :
                NPointDomain d n -> Complex) u))
          l (nhds (Wadj ((psi0).1 : SchwartzNPoint d n))) := by
      -- Use `SCV.tube_boundaryValueData_moving_of_fixed` with the transported
      -- adjacent boundary functional `Wadj`, not with the deterministic
      -- endpoint branch as upstream data, and feed in `hpsiMinus_move`.

    have hAdj_source_norm :
        Wadj ((psi0).1 : SchwartzNPoint d n) =
          OS.S n (D.toZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) phi) := by
      -- OS-I `(4.12)/(4.14)` source normalization.  After the raw seed has
      -- been transported to the terminal chart, the endpoint Wick/source
      -- section is
      -- `u ↦ bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k)))`.
      -- Use permutation covariance/E3 source normalization to identify this
      -- with the same zero-diagonal Schwinger functional as the ordinary
      -- side.

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
    (tendstoUniformlyOn_singleton_iff_tendsto
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
  source-side Schwinger limit for the signed cutoff families.
* `SCV.tube_boundaryValueData_moving_of_fixed` and
  `bvt_boundary_values_moving` upgrade fixed-test boundary values to moving
  tests after a boundary CLM has already been selected.
* `BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn`
  and
  `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`
  convert a proved source zero representation into the flat EOW seed.

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

Lean implementation leaves still to be proved inline:

* the ordinary `(4.1)` branch/source asymptotic transfer, with the ordinary
  endpoint chain and source/flat side-family identification unfolded.
* the raw-adjacent `(4.12)` branch/source asymptotic transfer, with the raw
  `OmegaSeed412/BSeed412` provenance retained until the terminal endpoint.
* the adjacent analytic-element uniqueness seed in the finite gallery, unless
  it is replaced by an explicit proof that does not use `Fdet` as upstream
  data.

Until these three bullets are proved in the proof body, a public horizontal
pairing zero theorem would be premature.  Do not split out that theorem now.
The current implementation target is the in-body proof of the two asymptotic
transfers inside the upstream `hadj412`
flat real-Jost crossing, followed immediately by the already checked
source-to-flat reducer and local EOW bridge.  Any production lemma that
assumes the flat zero, assumes either asymptotic transfer, assumes `Hdiff`,
assumes `Wadj`, or assumes a common-boundary CLM is still wrapper churn.

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
--   `(4.14)` source normalization.

-- Adjacent:
--   raw `OmegaSeed412/BSeed412` seed -> adjacent one-branch chain ->
--   terminal endpoint equality -> minus sheet membership ->
--   checked source-side pullback -> moving boundary value ->
--   `(4.12)/(4.14)` source normalization.
```

The final uniform-on-singleton asymptotic statements are then obtained by the
checked singleton bridge, not by a new public theorem:

```lean
have hPlus_asymptotic := by
  simpa [Keta] using
    (tendstoUniformlyOn_singleton_iff_tendsto
      (F := fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta)
      (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (p := l) (x := eta0)).2 hPlus_asymptotic_eta0

have hMinus_asymptotic := by
  simpa [Keta] using
    (tendstoUniformlyOn_singleton_iff_tendsto
      (F := fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
      (f := fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (p := l) (x := eta0)).2 hMinus_asymptotic_eta0
```

The flat real-Jost EOW case split occurs only after these two `have`s: combine
`hPlus_asymptotic`/`hMinus_asymptotic` with the checked source-side common
Schwinger limits, use `SCV.eq_zeroHeight_of_common_sideLimit`, inline the
`integral_sub`/ring rewrite from `AdjEdge = OrdEdge`, and immediately feed the
result to the checked source-to-flat reducer.  There is no exported wrapper
between the OS-I transfer and the `hadj412` local EOW seed.

Deep Research interaction
`v1_ChdtVklJYXN1V0E2S1AyOG9QbjdlaTZBYxIXbVZJSWFzdVdBNktQMjhvUG43ZWk2QWM`
completed on 2026-05-16 and supports this dependency order: the source zero
representation is non-circular exactly when `hhorizontal_zero` is proved by a
direct Fourier-Laplace/Jost boundary transfer.  The currently Lean-ready shape
of that transfer is the side-height form above; a finite-height compact
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
  refine ⟨W, isOpen_ball, by simpa [W] using Metric.mem_ball_self hr_pos,
    hball_sub, ?_⟩
  intro z hzW
  exact (Aord (hball_sub hzW).1).trans (Bord (hball_sub hzW).2).symm
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
  -- Build the finite gallery:
  --   reverse AadjChain to `OmegaAdj0`,
  --   use the common seed equality with `BAdj0`,
  --   follow BadjChain to B.
  -- Build this gallery in place using the same prefix-overlap induction used
  -- for `hadj412`: every inserted carrier is a metric ball, every branch is
  -- holomorphic on its carrier, and every nonempty overlap receives an open
  -- equality seed from retained raw-adjacent provenance.  The terminal local
  -- seed is then the seed supplied by the last prefix step.
```

This is just the same finite gallery induction already used to construct
`hadj412`; it consumes retained provenance and identity-theorem propagation.
It must not rewrite either initial adjacent branch to `extendF o permAct`
before the genuine `(4.12)` Wick trace has been transported.

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

This is the only case that consumes the proof-local OS-I `(4.14)` source
zero-representation blocker.  It must produce `hsource_zero_rep`, then the
checked reducer gives `h414_integrals`, before any exported `Hdiff`,
common-boundary CLM, or local `S'_n` branch exists.

Lean-ready branch-seed output:

```lean
have branch_seed
    (kind : BranchKind)
    (Achain Bchain : one_branch_chain_witness kind)
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

Cord : one_branch_chain_witness ordinary41
Cadj : one_branch_chain_witness adjacent412

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

## Lean-Start Checklist

Start Lean for `BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` only
when the proof script can point to these exact in-proof objects:

| Object | Needed before Lean |
| --- | --- |
| `OmegaOrd0`, `BOrd0` | Ordinary initial chart and trace to `OrdGlobal`. |
| `OmegaSeed412`, `BSeed412` | Checked raw `(4.12)` seed window at `zadj`, not at `zord`. |
| `hadj412`, producing `OmegaAdj0`, `BAdj0` | The genuine OS-I seed-to-Wick circuit from `zadj` through the common-edge flat EOW crossover and back to `zord`; this supplies the adjacent Wick trace and usable adjacent initial chart. |
| Initial metric-ball chart constructors | Checked for the ordinary Wick chart and corrected `(4.12)` seed chart by `BHW.OS45BHWJostHullData.ordinaryWick_metricBallChartInWindow` and `BHW.OS45BHWJostHullData.OS412SeedWindow_metricBallChartInWindow`. |
| Endpoint metric-ball chart constructors | Checked for the ordinary and adjacent horizontal common-edge endpoint charts by `BHW.OS45BHWJostHullData.ordinaryCommonEdge_metricBallChartInWindow` and `BHW.OS45BHWJostHullData.adjacentCommonEdge_metricBallChartInWindow`. |
| Endpoint difference metric-ball chart | Checked by `BHW.OS45BHWJostHullData.commonEdgeDifference_metricBallChartInWindow`; it gives the final horizontal `Adj - Ord` trace on an exact metric-ball carrier. |
| Metric-ball all-overlap propagation | Checked by `SCV.pairwise_eqOn_metric_ball_carriers_of_local_overlap_seeds`; it turns proof-local seeds on every nonempty pairwise overlap into full pairwise branch equality. |
| Ambient local zero-height flat EOW bridge | Checked by `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`; it transports local flat zero-height pairings to an ambient open seed in `ExtendedTube d n inter permutedExtendedTubeSector d n P.τ`. |
| Translated source-to-flat Jacobian algebra | Checked by `BHW.os45CommonEdgeFlatCLE_integral_comp_shift`; this is the real-translation plus CLE change of variables behind `x = e u ± eps • eta`. |
| Shifted/signed side cutoff removal | Checked by `BHW.OS45Figure24SourceCutoffData.toShiftedSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge`, `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_of_tsupport_subset_edge`, `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_eq_plain_eventually`, and `BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sourceWindow_support_and_eq_plain_eventually`; it discharges the pointwise cutoff-removal part of the side-height coordinate pullback after support has been shrunk. |
| Signed side-height branch/source pullback | Checked by `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shift`, `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_shiftedCLM`, `BHW.os45FlatCommonChart_branch_integral_eq_sourcePullback_sideZeroDiagonalCLM`, and `BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM`; it packages the translated CLE Jacobian and cutoff-removal algebra for the moving side tests without assuming any OS-I `(4.14)` boundary-value limit. |
| Source-side side-sheet argument | Checked by `BHW.os45FlatCommonChartSourceSide`, `BHW.os45FlatCommonChartBranch_sourceSide_eq_extendF`, and `BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff`; it names the exact source configuration obtained by undoing the quarter-turn, unfolds the flat branch value to `extendF`, and identifies the outgoing sheet-domain condition. |
| Eventual source-side sheet membership | Checked by `BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually`; for small positive side height, shifted support points land on the ordinary plus and raw-adjacent minus outgoing sheets. |
| Side branch integrability | Checked by `BHW.os45FlatCommonChart_branch_shifted_mul_integrable` and `BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually`; side-domain membership plus compact support gives the integrability hypothesis needed by the pullback theorem. |
| `one_branch_chain_witness ordinary41` | Terminal ordinary branch plus metric balls and seeds. |
| `one_branch_chain_witness adjacent412` | Terminal adjacent branch plus metric balls and seeds. |
| `local_transfer ordinary-sector` | Seed by equality with `OrdGlobal`. |
| `local_transfer adjacent-sector` | Seed from retained transported `(4.12)` provenance; no deterministic adjacent branch. |
| `local_transfer flat` | Non-circular flat EOW packet: first prove the horizontal compact-test zero by the ordinary and raw-adjacent branch/source asymptotic transfers plus the checked common source limit, giving `hsource_zero_rep`; then use the checked source-to-flat reducer, checked ordinary-edge representation, and checked ambient local zero-height bridge.  Source/CLE/Jacobian facts are coordinate audits only. |
| ordinary branch/source transfer | Proof-local OS-I `(4.14)` side-height transfer for the ordinary `(4.1)` element; it must prove `BranchPlusSide - SourcePlusSide -> 0`, not assume a zero-height equality or Schwinger normalization. |
| raw-adjacent branch/source transfer | Proof-local OS-I `(4.14)` side-height transfer for the transported raw adjacent `(4.12)` element; `extendF o permAct` may be used only after the raw seed has reached the endpoint chart. |
| `branch_seed ordinary41` | Proof-local all-overlap finite-gallery induction yielding `Word`. |
| `branch_seed adjacent412` | Proof-local all-overlap finite-gallery induction yielding `Wadj`. |
| `overlap_eq` | Difference equality on `A.N inter B.N` using the checked two-seed SCV helper. |
| `Ucx`, `Hdiff` | Direct gluing after all pairwise overlaps are proved. |

If any of these entries is unavailable, the next step is still proof-doc or
support-lemma work, not a public wrapper theorem.
