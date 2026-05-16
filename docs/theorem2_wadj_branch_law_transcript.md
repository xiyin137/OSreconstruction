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
  ...

have hadj_seed :
    exists Wadj : Set (Fin n -> Fin (d + 1) -> Complex),
      IsOpen Wadj /\
      z0 in Wadj /\
      Wadj <= A.N inter B.N /\
      Set.EqOn A.Adj B.Adj Wadj := by
  ...
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
  { z | BHW.permAct (d := d) P.tau z in BHW.ForwardTube d n } inter H.OmegaJ

BSeed412 z :=
  bvt_F OS lgc n (BHW.permAct (d := d) P.tau z)
```

This raw seed window is centered at the genuine adjacent seed point
`zadj = BHW.permAct P.tau zord`, not at the ordinary Wick point `zord`.
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
    bvt_F OS lgc n (fun k => wickRotatePoint (x (P.tau k)))

seed412 :
  exists Wseed : Set (Fin n -> Fin (d + 1) -> Complex),
    IsOpen Wseed /\
    Wseed.Nonempty /\
    Wseed <= OmegaAdj0 inter OmegaSeed412 /\
    Set.EqOn BAdj0 BSeed412 Wseed
```

The terminal adjacent branch is compared on:

```text
AdjSheet := BHW.permutedExtendedTubeSector d n P.tau
```

There is no upstream global formula for the adjacent branch in this stage.
The later deterministic branch using `extendF` after the permutation action is
downstream-only for Stage A.

The flat bridge uses the checked flat common-chart domains:

```text
FlatPlus  := BHW.os45FlatCommonChartOmega d n 1
FlatMinus := BHW.os45FlatCommonChartOmega d n (P.tau.symm * 1)
FlatEdge  := BHW.os45FlatCommonChartEdgeSet d n P 1
FlatCone  := BHW.os45FlatCommonChartCone d n
```

and the checked ambient bridge:

```lean
BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_continuousBoundaryOn
BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
```

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
  BHW.permAct (d := d) P.tau zord
let padj : Fin n -> Fin (d + 1) -> Complex :=
  BHW.permAct (d := d) P.tau pord

let OmegaSeed412 : Set (Fin n -> Fin (d + 1) -> Complex) :=
  {z | BHW.permAct (d := d) P.tau z in BHW.ForwardTube d n} inter H.OmegaJ

let BSeed412 : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.tau z)
```

Checked seed data already available:

```lean
have hseed_mem : zadj in OmegaSeed412 := by
  -- rewrite zord = fun k => wickRotatePoint (x k)
  -- rewrite zadj = fun k => wickRotatePoint (x (P.tau k))
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
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.tau k))) /\
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
3. **Flat common-edge crossover from `padj` to `pord`.**  Pull flat tests to
   the source window, use the checked
   `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick`, convert
   it to the local zero-height pairings, and call
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
2. `flat_zero_height_pairings_from_414`: for a local flat edge window `E`,
   construct `Tlocal`, `hzero_plus`, and `hzero_minus` from the ordinary
   `(4.1)` side, the genuine adjacent `(4.12)` side, and the checked
   source-pairing equality
   `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick`.
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
subproofs above.  It is not yet a closed proof: the live mathematical work is
now isolated in the adjacent analytic-element uniqueness seed and in the two
boundary-value trace-transfer blocks below.  The names below are local `have`
blocks inside the eventual proof of
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
      BHW.permutedExtendedTubeSector d n P.tau \cap H.OmegaJ
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
          BHW.permutedExtendedTubeSector d n P.tau \cap H.OmegaJ) /\
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
{z | BHW.permAct (d := d) P.tau z in BHW.ForwardTube d n} inter H.OmegaJ.
```

That raw window is the correct OS-I initial germ, but it is not by itself the
two-sheet overlap carrier needed for the Figure-2-4 gallery.  Before inserting
the seed chart into `Adj412ChartProv`, the proof must shrink the raw metric
ball using the checked point membership

```lean
H.OS412Seed_mem_initialSectorOverlap x hxP :
  BHW.permAct (d := d) P.tau (fun k => wickRotatePoint (x k)) in
    BHW.ExtendedTube d n inter BHW.permutedExtendedTubeSector d n P.tau
```

and the openness of both sheets.  The resulting first gallery carrier is:

```lean
let zseed := BHW.permAct (d := d) P.tau (fun k => wickRotatePoint (x k))
let SeedOverlap :=
  rawSeedCarrier inter BHW.ExtendedTube d n inter
    BHW.permutedExtendedTubeSector d n P.tau

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
      BHW.permutedExtendedTubeSector d n P.tau inter H.OmegaJ := by
  intro z hz
  have hz' := hseed_ball_sub hz
  exact <hz'.2.1, hz'.2.2, hz'.1.2>

have hBseed_holo : DifferentiableOn Complex Bseed Cseed := by
  exact rawSeed_holo.mono (fun z hz => (hseed_ball_sub hz).1)

have hBseed_trace :
    Bseed zseed = bvt_F OS lgc n (fun k => wickRotatePoint (x (P.tau k))) := by
  exact rawSeed_trace
```

This shrink is mathematical work, not a wrapper: it fixes the exact incoming
sheet domain for the genuine adjacent `(4.12)` chain.  It also explains why
the active route must not use the later deterministic adjacent branch as an
upstream seed.

### `flat_zero_height_pairings_from_414`

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
have flat_zero_height_pairings_from_414 :
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
            (P.tau.symm * (1 : Equiv.Perm (Fin n)))
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
            (P.tau.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : Complex)) * phi x) =
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : Complex)) * phi x) := by
    intro phi hphi_compact hphiE
    -- This is the flat `(4.14)` output of the proof-local OS-I transfer,
    -- not a finite-side-height Schwinger identity.  Its Lean proof must be
    -- constructed inside `BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`:
    --
    -- * pull `phi` back by `D.toSchwartzNPointCLM 1`;
    -- * use the checked source-side compact-test equality
    --   `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick`;
    -- * for signed side source-test families, use the checked common source
    --   limit
    --   `BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`;
    -- * transport the current ordinary and genuine adjacent analytic-element
    --   side boundary traces through the common-edge CLE/cutoff support
    --   formulas;
    -- * apply the local distributional uniqueness theorem on the current
    --   source window to identify the zero-height flat traces.
    --
    -- Inline the Lean-facing flat `(4.14)` trace calculation below at this
    -- point.  It constructs the two branch-side side families, the
    -- Jacobian-scaled source-side families, the checked common source limit,
    -- the two proof-local branch-to-source asymptotic transfers, and then
    -- applies `SCV.eq_zeroHeight_of_common_sideLimit`.  The local object
    -- produced by that inline block is named `h414_integrals_phi` below only
    -- for readability; it is not a public theorem.
    exact h414_integrals_phi

  have hzero_minus :
      forall phi, HasCompactSupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) ->
        tsupport (phi :
          BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
        (integral fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.tau.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : Complex)) * phi x) =
          Tlocal phi := by
    intro phi hphi_compact hphiE
    exact (h414_integrals phi hphi_compact hphiE).trans
      (hzero_plus phi hphi_compact hphiE)

  exact <hE_open, hE_sub, Tlocal, hzero_plus, hzero_minus>
```

The flat block has no named theorem placeholder left.  The proof-local
transition is the inline compact-test calculation expanded next:

```text
proof-local flat transition:
  ∫ Fminus0 x * phi x = ∫ Fplus0 x * phi x
  for every compactly supported flat test with support in the current edge
  image E = os45CommonEdgeFlatCLE d n 1 '' Ulocal.

checked inputs used inside the proof:
  BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick,
  BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger,
  BHW.OS45Figure24SourceCutoffData.toSchwartzNPointCLM_* support/accessor
  lemmas, BHW.os45FlatCommonChart_commonBoundaryDifference_integral_eq_sourcePullback,
  BHW.os45CommonEdgeFlatJacobianAbs, and
  SCV.eq_zeroHeight_of_common_sideLimit.
```

The next Lean target is therefore not a finite-height side theorem.  It is the
local transfer theorem that produces the current adjacent `(4.12)` analytic
element at the flat endpoint, identifies its signed side boundary traces with
the checked source-side common Schwinger limit, and supplies the compact-test
equality above.
A helper that assumes the equality above, assumes zero-height equality, or
mentions an already-built `Hdiff`/`Wadj` would be a wrapper and should not be
added.

#### Lean-facing flat `(4.14)` trace calculation

The flat calculation must be written in the proof body in the following
shape.  The important point is that the branch-side finite-height families are
not asserted to equal arbitrary Schwinger side tests.  Instead, the proof uses
the current ordinary `(4.1)` and genuine adjacent `(4.12)` analytic elements to
transport exactly two signed boundary traces to the already checked source
families.

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
    (P.tau.symm * (1 : Equiv.Perm (Fin n))) (SCV.realEmbed x)
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
      (P.tau.symm * (1 : Equiv.Perm (Fin n)))
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
      bvt_F OS lgc n (fun k => wickRotatePoint (u (P.tau k))) *
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
  exact ordinary41_side_trace_asymptotic_to_source
    chainOrd endpointOrd D phi hphi_compact hphiE

have hMinus_asymptotic :
    TendstoUniformlyOn
      (fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta)
      (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
  exact adjacent412_side_trace_asymptotic_to_source
    chainAdj endpointAdj D phi hphi_compact hphiE
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

The two asymptotic blocks must be proved with the following proof-local shapes.
They should not be public OS45 wrapper theorems until their proof bodies are
complete, because their statements expose exactly the remaining mathematical
work.

Ordinary side:

```lean
have ordinary41_side_trace_asymptotic_to_source :
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
  have hOrd_bv :
      TendstoUniformlyOn
        (fun eps eta =>
          BranchPlusSide eps eta - SourcePlusSide eps eta)
        (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
    -- Use `D.toSideZeroDiagonalCLM_apply` to identify the source test
    -- integrand after the common-edge CLE change of variables, and use the
    -- `(4.1)` boundary-value convergence of `bvt_F`.
    exact ordinary41_boundaryValue_uniform_on_sideCutoffTests
      endpointOrd hOrd_terminal_eq_extendF D Keta hKeta_compact
      hKeta_cone phi hphi_compact hphiE

  exact hOrd_bv
```

Adjacent side:

```lean
have adjacent412_side_trace_asymptotic_to_source :
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
  --    `BHW.os45FlatCommonChartOmega d n (P.tau.symm * 1)`.
  obtain <r_side, hr_side, hplus_side_mem, hminus_side_mem> :=
    BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
      (d := d) hd (P := P)
      (tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex))
      hphi_compact.isCompact hphiE
      Keta hKeta_compact hKeta_cone

  -- 2. Transport the genuine `(4.12)` analytic element to the endpoint
  --    adjacent common-edge chart.  The endpoint chart may be represented by
  --    `z => BHW.extendF (bvt_F OS lgc n) (BHW.permAct P.tau z)`, but only
  --    after the chain has proved equality with the branch transported from
  --    Cseed/Bseed.
  have hAdj_terminal_eq_endpoint :
      Set.EqOn endpointAdj.branch
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.tau z))
        endpointAdj.carrier := by
    exact chainAdj.terminal_eq_transported_adjacent_endpoint

  have hAdj_endpoint_trace :
      endpointAdj.branch endpointAdj.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.tau.symm * (1 : Equiv.Perm (Fin n)))
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
  have hAdj_bv :
      TendstoUniformlyOn
        (fun eps eta =>
          BranchMinusSide eps eta - SourceMinusSide eps eta)
        (fun _ : BHW.OS45FlatCommonChartReal d n => 0)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) Keta := by
    exact adjacent412_boundaryValue_uniform_on_sideCutoffTests
      chainAdj endpointAdj hAdj_terminal_eq_endpoint D Keta
      hKeta_compact hKeta_cone phi hphi_compact hphiE

  exact hAdj_bv
```

The two named boundary-value lemmas in these skeletons are the actual remaining
mathematical targets.  They must prove uniform convergence for the moving
cutoff-pulled tests using the OS linear-growth/boundary-value machinery and the
stored analytic-element provenance.  They may use checked pointwise formulas
such as `D.toSideZeroDiagonalCLM_apply`, but they must not assume a flat EOW
seed, `Hdiff`, `Wadj`, or the local `S'_n` branch.

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
--   TendstoUniformlyOn (fun eps eta => BranchPlusSide eps eta - SourcePlusSide eps eta) ...
--   TendstoUniformlyOn (fun eps eta => BranchMinusSide eps eta - SourceMinusSide eps eta) ...
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
  flat_zero_height_pairings_from_414 hUlocal_open hUlocal_sub u0 hu0

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
  all inside ExtendedTube inter permutedExtendedTubeSector P.tau

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
  --    flat_zero_height_pairings_from_414 and then the checked ambient
  --    local zero-height bridge.
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
      bvt_F OS lgc n (fun k => wickRotatePoint (x (P.tau k))) := by
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
| Adjacent sector | `BHW.permutedExtendedTubeSector d n P.tau` | raw `(4.12)` seed window `H.OS412SeedWindow_metricBallChartInWindow`, seed obstruction `H.ordinaryWick_not_mem_OS412SeedWindow`, corridor geometry `BHW.os45Figure24_joined_adjacentWick_to_adjLift0_initialSectorOverlap`, `BHW.os45Figure24_joined_adjLift0_to_adjLift1_initialSectorOverlap`, `BHW.os45Figure24_joined_adjLift_to_permActIdentityPath_initialSectorOverlap`, `BHW.os45Figure24_joined_permActOrdinaryWick_to_permActCommonEdge_initialSectorOverlap`, and endpoint bookkeeping `H.adjacentCommonEdge_metricBallChartInWindow` | the branch-law equality that transports the genuine `(4.12)` analytic element; this is not `extendF o permAct` as an initial seed |
| Flat real-Jost, upstream inside `hadj412` | plus side `BHW.os45FlatCommonChartOmega d n 1`, minus side `BHW.os45FlatCommonChartOmega d n (P.tau.symm * 1)`, edge `os45CommonEdgeFlatCLE d n 1 '' Ulocal` | source-window support, source common Schwinger limit, `SCV.eq_zeroHeight_of_common_sideLimit`, and `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM` after the two zero-height pairings are proved | the OS-I `(4.14)` compact-test boundary transfer for the current ordinary `(4.1)` and transported adjacent `(4.12)` elements |
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
AdjSheet = BHW.permutedExtendedTubeSector d n P.tau
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
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.tau k))) := by
  -- output of the raw `(4.12)` seed-to-ordinary-Wick transport

have hadj412_common_trace :
    forall u, u in Ulocal ->
      Badj412
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.tau
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)))) := by
  -- terminal adjacent common-edge chart trace, after transporting the same
  -- genuine `(4.12)` element to the endpoint-centered chart
```

It is invalid to instantiate the same Wick-seed theorem with

```lean
fun z => BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) P.tau z)
```

as the adjacent branch before `hadj412_wick_trace` has been proved.  At
`z = fun k => wickRotatePoint (u k)`, that would require normalizing
`extendF` at `BHW.permAct P.tau z`; this is exactly the missing `(4.12)`
transport and cannot be obtained by `extendF_eq_on_forwardTube`.

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
FlatMinus = BHW.os45FlatCommonChartOmega d n (P.tau.symm * 1)
```

Edge:

```text
E <= BHW.os45FlatCommonChartEdgeSet d n P 1
```

The proof order is binding:

1. Build the source cutoff `Dcut` and pull the flat test to the source
   variables.
2. Use the checked source-side Schwinger limit
   `BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger`
   for the signed side source-test families.  The checked compact-test equality
   `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick` remains the
   zero-height source anchor, but it is not by itself an EOW seed.
3. Prove the two local branch-to-source asymptotic transfer congruences:
   ordinary `(4.1)` plus-side trace to the plus source family, and transported
   genuine `(4.12)` minus-side trace to the minus source family.
4. Apply `SCV.eq_zeroHeight_of_common_sideLimit` to get the flat
   zero-height compact-test equality
   `∫ Fminus0 * phi = ∫ Fplus0 * phi`.
5. Convert the zero-height compact-test equality into the two local
   representations against `Tlocal`; this is where the checked ordinary-edge
   CLM representation supplies `hzero_plus`, and the equality from step 4
   supplies `hzero_minus`.
6. Feed the resulting local zero-height pairings into the checked ambient
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
    (P.tau.symm * (1 : Equiv.Perm (Fin n))) (fun a => (x a : Complex))

have hE_open : IsOpen E := by
  -- image openness from os45CommonEdgeFlatCLE and Ulocal_open

have hE_sub :
    E <= BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n)) := by
  -- BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff and Ulocal <= P.V

have h414_integrals :
    forall phi : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex,
      HasCompactSupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ->
      tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) <= E ->
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fminus0 x * phi x) =
      (integral fun x : BHW.OS45FlatCommonChartReal d n =>
        Fplus0 x * phi x) := by
  -- This is the real OS-I `(4.14)` compact-test subproof for the current
  -- ordinary `(4.1)` and transported adjacent `(4.12)` analytic elements.
  -- It is proved by the signed side-limit dispatcher above:
  --   source common Schwinger limit
  --   + ordinary41_side_trace_asymptotic_to_source
  --   + adjacent412_side_trace_asymptotic_to_source
  --   + SCV.eq_zeroHeight_of_common_sideLimit.
  -- A direct call to a source-pairing equality here would be too weak unless
  -- the two analytic-element side traces have already been transported.

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
       BHW.permutedExtendedTubeSector d n P.tau /\
  Set.EqOn
    (BHW.extendF (bvt_F OS lgc n))
    (fun z =>
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) P.tau z))
    W
```

Inside Stage A this seed is used only as the local comparison seed for the
flat crossing.  It is not a common-boundary CLM and it is not a local SPrime
branch.

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
          (P.tau.symm * (1 : Equiv.Perm (Fin n)))
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
| Ambient local zero-height flat EOW bridge | Checked by `BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM`; it transports local flat zero-height pairings to an ambient open seed in `ExtendedTube d n inter permutedExtendedTubeSector d n P.tau`. |
| `one_branch_chain_witness ordinary41` | Terminal ordinary branch plus metric balls and seeds. |
| `one_branch_chain_witness adjacent412` | Terminal adjacent branch plus metric balls and seeds. |
| `local_transfer ordinary-sector` | Seed by equality with `OrdGlobal`. |
| `local_transfer adjacent-sector` | Seed from retained transported `(4.12)` provenance; no deterministic adjacent branch. |
| `local_transfer flat` | Non-circular flat EOW packet using the upstream `(4.14)` compact-test transfer, Jacobian-scaled source side families, and the checked ambient local zero-height bridge. |
| `branch_seed ordinary41` | Proof-local all-overlap finite-gallery induction yielding `Word`. |
| `branch_seed adjacent412` | Proof-local all-overlap finite-gallery induction yielding `Wadj`. |
| `overlap_eq` | Difference equality on `A.N inter B.N` using the checked two-seed SCV helper. |
| `Ucx`, `Hdiff` | Direct gluing after all pairwise overlaps are proved. |

If any of these entries is unavailable, the next step is still proof-doc or
support-lemma work, not a public wrapper theorem.
