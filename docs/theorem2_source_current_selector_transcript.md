# Theorem 2 Source-Current Selector Transcript

Status: focused live transcript for the two remaining source-current holes in
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`.

This note is not a new theorem surface and not a closure declaration.  Its
purpose is to make the direct producer body Lean-facing before returning to
Lean.  The implementation should expand these steps as local `have`s inside
the Hdiff producer, except for neutral analytic/topological helpers that do
not mention `Hdiff`, `Word`, `Wadj`, zero-height equality, or theorem 2.

## Exact Live Goals

Inside the current `hzero_minus` body, after fixing `eta0`, `D`, `psi0`, and
the source compact packet, the two remaining goals are:

```lean
let l : Filter Real := nhdsWithin (0 : Real) (Set.Ioi 0)

have hOrd_side_current :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta0 u) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta0 phi).1 :
              SchwartzNPoint d n) : NPointDomain d n -> Complex) u))
      l
      (nhds (OS.S n (D.toZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) phi))) := by
  -- direct ordinary `(4.1)/(4.14)` source-current selector

let tauOut : Equiv.Perm (Fin n) :=
  (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm

have hAdj_side_current :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) tauOut
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta0 u)) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta0 phi).1 :
              SchwartzNPoint d n) : NPointDomain d n -> Complex) u))
      l
      (nhds (OS.S n (D.toZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) phi))) := by
  -- direct retained raw `(4.12)/(4.14)` source-current selector
```

The endpoint DCTs already present in the body are the final moving-test
upgrade, not the chart-transport proof.  The missing work is first to select
the fixed flat translated-boundary value by the ordinary `(4.1)` and retained
raw `(4.12)` one-branch chains.  Fixed endpoint DCT then identifies the
zero-height endpoint with that selected value, and only then do the moving
endpoint DCTs close the displayed side-current families.

## Fixed Local Objects

Use exactly these local definitions.  Do not replace the raw adjacent seed by a
downstream deterministic branch.

```lean
let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))

let psi0 : SchwartzNPoint d n :=
  (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi).1

-- `psi0Flat` and the common-edge Jacobian are active in the fixed selector.
-- They belong to the flat translated-boundary selection and scalar
-- cancellation layer, before the moving endpoint DCTs are used.

let sourceSide (sgn eps : Real)
    (eta : BHW.OS45FlatCommonChartReal d n) (u : NPointDomain d n) :=
  BHW.os45FlatCommonChartSourceSide
    d n (1 : Equiv.Perm (Fin n)) sgn eps eta u

let sigmaOrd : Equiv.Perm (Fin n) := 1
let sigmaAdj : Equiv.Perm (Fin n) :=
  P.τ.symm * (1 : Equiv.Perm (Fin n))

have hSigmaAdj_symm : sigmaAdj.symm = P.τ := by
  simp [sigmaAdj]

let gammaOrd : unitInterval -> Fin n -> Fin (d + 1) -> Complex :=
  BHW.os45Figure24IdentityPath (d := d) (n := n) x

let gammaAdjSeed : unitInterval -> Fin n -> Fin (d + 1) -> Complex :=
  fun t => BHW.permAct (d := d) P.τ (gammaOrd t)

let OmegaSeed412 : Set (Fin n -> Fin (d + 1) -> Complex) :=
  {z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ

let BSeed412 : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
```

The raw current path starts at `gammaAdjSeed 0`.  The statement
`gammaOrd 0 ∈ OmegaSeed412` is false in the current Lean facts and must not be
used.

## Existing Inputs To Consume

The following inputs are already part of the local file or imported support
and should be consumed directly.

```lean
ordinary41_fixed_test_boundaryValue_extendF
ordinary41_moving_boundaryValue_extendF
raw412_fixed_test_boundaryValue
raw412_moving_boundaryValue

BHW.OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
BHW.os45FlatCommonChart_wickSection_sourcePairing_eq_schwinger
BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger
BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest
BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
BHW.eventually_integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport

BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM_flatPullback_support
BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually
BHW.OS45Figure24SourceCutoffData.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero

BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually
BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
BHW.permAct_os45FlatCommonChartSourceSide_zero

BHW.OS45BHWJostHullData.ordinaryWick_pointedChartInWindow
BHW.OS45BHWJostHullData.OS412SeedWindow_pointedChart
PointedMetricBranchChart.eqOn_inter_of_seed
bvt_euclidean_restriction
```

The first four private boundary-value leaves are only raw tube-ray inputs.
They do not by themselves prove either displayed source-current goal.  They
become useful only after the local chain has related the incoming ray to the
terminal flat/source-side family.  Likewise,
`D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger` is a checked
source-current normalization/support package; it must not be treated as the
finite chart-transport selector.

## Checked Carrier Facts To Use

The selector must be written against the carrier facts that are actually
checked in `OSToWightmanLocalityOS45Figure24Hdiff.lean`; do not invent a
generic chain packet.

Ordinary-sector charts have the `OrdModelAtZ0` shape:

```lean
OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) A
```

They are produced by the checked pointed adapters
`H.ordinaryWick_pointedChartInWindow` and
`H.ordinaryCommonEdge_pointedChartInWindow`.  Their load-bearing fields are

```lean
A.carrier ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W
Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier
```

An ordinary edge is therefore local and direct:

```lean
have hedge :
    PointedSeedEdge z0 A.carrier B.carrier A.branch B.branch :=
  pointed_seed_edge_of_common_model
    A.carrier_open B.carrier_open hA.z0_mem hB.z0_mem
    hA.eq_ord hB.eq_ord
```

Raw-adjacent-sector charts use retained `(4.12)` provenance, not the endpoint
deterministic branch.  The incoming chart is produced by
`H.OS412SeedWindow_pointedChart` at
`zadj = gammaAdjSeed 0`, with

```lean
A.carrier ⊆
  (({z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) ∩
    (BHW.ExtendedTube d n ∩
      BHW.permutedExtendedTubeSector d n P.τ))
Set.EqOn A.branch BSeed412 A.carrier
```

Interior raw edges should be represented as `RawRetargetAtZ0` data against a
single local raw chart:

```lean
RawRetargetAtZ0 d n z0 A rawLocal
```

and the actual edge consumed by the selector is

```lean
hA_adj.edge_to_raw :
  PointedSeedEdge z0 A.carrier rawLocal.carrier A.branch rawLocal.branch
```

If two raw charts both retarget to the same `rawLocal`, use
`os45_pointed_gallery_pair_one_one` or the equivalent inline one-step gallery;
do not call `LocalOverlapAtZ0.flat_plus_minus`,
`LocalOverlapAtZ0.flat_minus_plus`, or
`localOverlapAtZ0_galleryPair` in the source-current selector.  Those flat
constructors call
`flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM`, whose inputs
include the zero-height pairings being proved.

The terminal raw-to-flat-minus rewrite is not an incoming chart.  It is a
support-local final step after the retained raw chain has reached the terminal
flat-minus expression and after the eventual sheet membership has proved

```lean
BHW.permAct (d := d) P.τ
  (sourceSide (-1 : Real) eps eta0 u) ∈ BHW.ForwardTube d n
```

on the compact support.  Only there may
`BHW.extendF_eq_on_forwardTube` rewrite the terminal expression to the
displayed `extendF ∘ permAct` form consumed by the source-side DCT.

Every selector edge then has the same identity-theorem use:

```lean
have hEq_inter :
    Set.EqOn A.branch B.branch (A.carrier ∩ B.carrier) :=
  PointedMetricBranchChart.eqOn_inter_of_seed A B
    ⟨edge.W, edge.W_open, edge.z0_mem, edge.W_sub, edge.eqOn⟩
```

The edge proof is incomplete unless this promoted carrier-intersection
equality is the equality used inside `integral_congr_ae`.

## Source Support Packet

The fixed selector and the later moving endpoint DCT must use compatible
source support.  The fixed selector works with the compact flat test
`psi0Flat` and its translated supports.  The moving endpoint DCT works with the
live signed `D.toSideZeroDiagonalCLM` tests.  Both are tied to the same source
window packet in the current `Hdiff` body:

```lean
let Ssrc : Set (NPointDomain d n) :=
  e.symm '' tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex)

obtain ⟨Ksrc, hKsrc_compact, hSsrc_int, hKsrcU⟩ :=
  exists_compact_between hSsrc_compact hU_open hSsrcU

let Usrc : Set (NPointDomain d n) := interior Ksrc

have hphiUsrc :
    tsupport (phi : BHW.OS45FlatCommonChartReal d n -> Complex) ⊆
      e '' Usrc := by
  -- already present as `hφUsrc` in the current file
```

Before using the moving endpoint DCT, add the signed side-test support
eventuality and specialize it to the chosen `eta0`:

```lean
have hcurrent_tsupport_Usrc :
    ∀ᶠ eps in l, ∀ eta ∈ Keta,
      tsupport ((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta phi).1 :
          NPointDomain d n -> Complex) ⊆ Usrc ∧
      tsupport ((D.toSideZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta phi).1 :
          NPointDomain d n -> Complex) ⊆ Usrc := by
  simpa [l] using
    D.toSideZeroDiagonalCLM_tsupport_subset_image_eventually
      hUsrc_open Keta hKeta phi hphi_compact hphiUsrc

have hcurrent_support_Ksrc_ord :
    ∀ᶠ eps in l,
      Function.support
        (((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta0 phi).1 :
            SchwartzNPoint d n) : NPointDomain d n -> Complex) ⊆
        Ksrc := by
  filter_upwards [hcurrent_tsupport_Usrc] with eps heps u hu
  exact hUsrc_sub_Ksrc ((heps eta0 hEta0).1 (subset_tsupport _ hu))

have hcurrent_support_Ksrc_adj :
    ∀ᶠ eps in l,
      Function.support
        (((D.toSideZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta0 phi).1 :
            SchwartzNPoint d n) : NPointDomain d n -> Complex) ⊆
        Ksrc := by
  filter_upwards [hcurrent_tsupport_Usrc] with eps heps u hu
  exact hUsrc_sub_Ksrc ((heps eta0 hEta0).2 (subset_tsupport _ hu))
```

This support object is for the endpoint/moving-test layer.  The edge
`integral_congr_ae` steps inside `hflatOrd_selected` and `hflatAdj_selected`
use the compact support of `psi0Flat` and the translated-test collar described
in the finite selector section below.  If the implementation instead proves
local fixed selectors on a finite source cover, then split the test first and
prove both the fixed `psi0Flat` collar and the moving endpoint support packet
for each localized piece; do not run a chart chain centered at a single source
point against an unlocalized compact integral.

## Active Proof Shape

Correction, 2026-05-18: do **not** prove the two moving-current holes by a
finite induction that transports the checked Wick current pairings directly
from the Wick endpoint to the terminal `sourceSide` endpoint.  That would
mistake analytic continuation for equality of branch values at different
points.  The finite chart induction belongs one level earlier: it selects the
fixed flat translated-boundary limit.  The live moving-current holes then close
by the already checked endpoint DCTs.

The direct in-body proof has three layers:

1. Fixed source-side selector:
   prove `Tendsto OrdFixed l (nhds Lcur)` and
   `Tendsto AdjFixed l (nhds Lcur)` by the one-branch flat translated-boundary
   selector, scalar cancellation, and endpoint normalization.
2. Fixed endpoint DCT:
   prove `Tendsto OrdFixed l (nhds OrdEndpoint)` and
   `Tendsto AdjFixed l (nhds AdjEndpoint)` with the checked source-side DCT
   for the fixed test `psi0`.
3. Moving endpoint DCT:
   use the already-present `hOrd_endpoint_DCT` and `hAdj_endpoint_DCT` for the
   moving `D.toSideZeroDiagonalCLM` tests, rewriting their endpoint values by
   uniqueness of limits from steps 1 and 2.

The theorem
`D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger` remains a
checked Wick-current normalization package, but it is not the active
chart-transport selector for these two holes.

## Fixed Outer Skeleton

Inside each live hole, use only local `have`s.  The common definitions are:

```lean
let Lcur : Complex :=
  OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi)

let sourceSide (sgn eps : Real)
    (eta : BHW.OS45FlatCommonChartReal d n) (u : NPointDomain d n) :=
  BHW.os45FlatCommonChartSourceSide
    d n (1 : Equiv.Perm (Fin n)) sgn eps eta u

let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))

let psi0 : SchwartzNPoint d n :=
  (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi).1

let psi0Flat : SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm)
    ((psi0 : SchwartzNPoint d n))

let pullFlatToSource :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex →L[Complex]
      SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex e

have hpull_psi0Flat : pullFlatToSource psi0Flat = psi0 := by
  simp [pullFlatToSource, psi0Flat, e]

obtain ⟨hpsi0Flat_compact, hpsi0Flat_edge⟩ :
    HasCompactSupport
        (psi0Flat : BHW.OS45FlatCommonChartReal d n -> Complex) ∧
      tsupport
        (psi0Flat : BHW.OS45FlatCommonChartReal d n -> Complex) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) := by
  simpa [psi0, psi0Flat, e] using
    D.toZeroDiagonalCLM_flatPullback_support
      (1 : Equiv.Perm (Fin n)) phi hφUsrc hKsrcU
```

The support input to `toZeroDiagonalCLM_flatPullback_support` is the source
window version `hφUsrc`, not merely `hφE`; this keeps the fixed selector and
the later moving endpoint DCT on the same compact current carrier.

### Ordinary Skeleton

```lean
let OrdFixed : Real -> Complex := fun eps =>
  ∫ u : NPointDomain d n,
    BHW.extendF (bvt_F OS lgc n)
      (sourceSide (1 : Real) eps eta0 u) *
    (psi0 : NPointDomain d n -> Complex) u

let OrdEndpoint : Complex :=
  ∫ u : NPointDomain d n,
    BHW.extendF (bvt_F OS lgc n)
      (sourceSide (1 : Real) 0 eta0 u) *
    (psi0 : NPointDomain d n -> Complex) u

have hOrd_fixed_selected :
    Tendsto OrdFixed l (nhds Lcur) := by
  -- section `Ordinary Fixed Selector` below

have hOrd_fixed_endpoint :
    Tendsto OrdFixed l (nhds OrdEndpoint) := by
  -- fixed-test endpoint DCT only.
  -- Use
  -- `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport`
  -- or the assembled fixed special case of
  -- `BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport`
  -- with constant `phi0 = psi0`.

have hOrd_endpoint_value : OrdEndpoint = Lcur :=
  tendsto_nhds_unique hOrd_fixed_endpoint hOrd_fixed_selected

have hOrd_side_current :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (sourceSide (1 : Real) eps eta0 u) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta0 phi).1 :
              SchwartzNPoint d n) : NPointDomain d n -> Complex) u))
      l (nhds Lcur) := by
  -- `hOrd_endpoint_DCT` is already present in the live Hdiff context.
  simpa [OrdEndpoint, sourceSide, hOrd_endpoint_value] using hOrd_endpoint_DCT
```

### Raw-Adjacent Skeleton

```lean
let tauOut : Equiv.Perm (Fin n) :=
  (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm

let sigmaAdj : Equiv.Perm (Fin n) :=
  P.τ.symm * (1 : Equiv.Perm (Fin n))

have hSigmaAdj_symm : sigmaAdj.symm = P.τ := by
  simp [sigmaAdj]

let AdjFixed : Real -> Complex := fun eps =>
  ∫ u : NPointDomain d n,
    BHW.extendF (bvt_F OS lgc n)
      (BHW.permAct (d := d) tauOut
        (sourceSide (-1 : Real) eps eta0 u)) *
    (psi0 : NPointDomain d n -> Complex) u

let AdjEndpoint : Complex :=
  ∫ u : NPointDomain d n,
    BHW.extendF (bvt_F OS lgc n)
      (BHW.permAct (d := d) tauOut
        (sourceSide (-1 : Real) 0 eta0 u)) *
    (psi0 : NPointDomain d n -> Complex) u

have hAdj_fixed_selected :
    Tendsto AdjFixed l (nhds Lcur) := by
  -- section `Raw-Adjacent Fixed Selector` below

have hAdj_fixed_endpoint :
    Tendsto AdjFixed l (nhds AdjEndpoint) := by
  -- fixed-test endpoint DCT with carrier
  -- `{z | BHW.permAct (d := d) tauOut z ∈ BHW.ExtendedTube d n}`.

have hAdj_endpoint_value : AdjEndpoint = Lcur :=
  tendsto_nhds_unique hAdj_fixed_endpoint hAdj_fixed_selected

have hAdj_side_current :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) tauOut
              (sourceSide (-1 : Real) eps eta0 u)) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (-1 : Real) eps eta0 phi).1 :
              SchwartzNPoint d n) : NPointDomain d n -> Complex) u))
      l (nhds Lcur) := by
  simpa [AdjEndpoint, sourceSide, tauOut, hAdj_endpoint_value] using
    hAdj_endpoint_DCT
```

The adjacent fixed selector starts from the retained raw `(4.12)` seed
`OmegaSeed412/BSeed412`; the displayed `extendF ∘ permAct` expression is only
the terminal normal form used after the raw chain reaches the outgoing sheet.

## Ordinary Fixed Selector

The hard ordinary selector proves `hOrd_fixed_selected`.  It should be expanded
inside the `hOrd_side_current` block:

```lean
let J : Complex := BHW.os45CommonEdgeFlatJacobianAbs n

let psiFlatOrd (eps : Real) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex :=
  SCV.translateSchwartz (-(eps • eta0)) psi0Flat

let FlatOrd : Real -> Complex := fun eps =>
  ∫ x : BHW.OS45FlatCommonChartReal d n,
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
      (fun a => (x a : Complex) + ((eps • eta0) a : Complex) * Complex.I) *
    psiFlatOrd eps x

have hflatOrd_selected :
    Tendsto FlatOrd l (nhds (J * Lcur)) := by
  -- finite flat-boundary selector:
  -- 1. build the ordinary one-branch chain from the `(4.1)` incoming chart;
  -- 2. base limit is the genuine ordinary OS-I boundary-value theorem, not
  --    the terminal `sourceSide` family;
  -- 3. promote every stored seed by
  --    `PointedMetricBranchChart.eqOn_inter_of_seed`;
  -- 4. use compact collars for the chart-local flat approach family;
  -- 5. terminal rewrite uses the ordinary flat plus branch above.

have hOrd_fixed_selected :
    Tendsto OrdFixed l (nhds Lcur) := by
  have hinteg :
      ∀ᶠ eps in l,
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun j =>
                (x j : Complex) + (((1 : Real) * eps) • eta0 j : Complex) *
                  Complex.I) *
            (SCV.translateSchwartz (-((1 : Real) * eps) • eta0) psi0Flat)
              (x + ((1 : Real) * eps) • eta0)) := by
    -- from `BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually`
    -- specialized to `psi0Flat`, `hpsi0Flat_compact`, `hpsi0Flat_edge`.
  have hcancel :=
    BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest
      (d := d) (n := n) OS lgc
      (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
      (1 : Real) eta0 psi0Flat
      hinteg hflatOrd_selected
  -- Rewrite the fixed source test by `hpull_psi0Flat`.
  simpa [OrdFixed, sourceSide, psi0Flat, pullFlatToSource,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, one_mul] using hcancel
```

The base normalization inside `hflatOrd_selected` eventually reduces to
`bvt_euclidean_restriction` for `D.toZeroDiagonalCLM 1 phi`, after the ordinary
chain trace has identified the selected fixed boundary functional with the
Wick pairing.

## Raw-Adjacent Fixed Selector

The raw-adjacent selector has the same scalar-cancellation shell but a different
incoming analytic element:

```lean
let OmegaSeed412 : Set (Fin n -> Fin (d + 1) -> Complex) :=
  {z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ

let BSeed412 : (Fin n -> Fin (d + 1) -> Complex) -> Complex :=
  fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)

let psiFlatAdj (eps : Real) :
    SchwartzMap (BHW.OS45FlatCommonChartReal d n) Complex :=
  SCV.translateSchwartz (-((-eps) • eta0)) psi0Flat

let FlatAdj : Real -> Complex := fun eps =>
  ∫ x : BHW.OS45FlatCommonChartReal d n,
    BHW.os45FlatCommonChartBranch d n OS lgc sigmaAdj
      (fun a => (x a : Complex) + (((-1 : Real) * eps) • eta0 a : Complex) *
        Complex.I) *
    psiFlatAdj eps x

have hflatAdj_selected :
    Tendsto FlatAdj l (nhds (J * Lcur)) := by
  -- finite flat-boundary selector:
  -- 1. base chart is `H.OS412SeedWindow_pointedChart` at
  --    `gammaAdjSeed 0`, model `BSeed412`;
  -- 2. interior edges preserve retained raw `(4.12)` provenance;
  -- 3. do not use the downstream flat plus/minus EOW seed;
  -- 4. terminal raw-to-flat-minus rewrite is support-local and happens only
  --    after the raw terminal chart is reached;
  -- 5. normalize the raw Wick trace with
  --    `BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger`.

have hAdj_fixed_selected :
    Tendsto AdjFixed l (nhds Lcur) := by
  have hinteg :
      ∀ᶠ eps in l,
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc sigmaAdj
              (fun j =>
                (x j : Complex) + (((-1 : Real) * eps) • eta0 j : Complex) *
                  Complex.I) *
            (SCV.translateSchwartz (-((-1 : Real) * eps) • eta0) psi0Flat)
              (x + ((-1 : Real) * eps) • eta0)) := by
    -- same checked integrability theorem, minus side.
  have hcancel :=
    BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest
      (d := d) (n := n) OS lgc
      sigmaAdj (1 : Equiv.Perm (Fin n))
      (-1 : Real) eta0 psi0Flat
      hinteg hflatAdj_selected
  simpa [AdjFixed, sourceSide, sigmaAdj, hSigmaAdj_symm, tauOut, psi0Flat,
    pullFlatToSource, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    one_mul] using hcancel
```

The raw endpoint normalization is not `extendF_eq_on_forwardTube` at the
incoming seed.  The terminal support-local rewrite to
`extendF (bvt_F) (permAct P.τ z)` happens only after the retained raw chain has
reached the terminal flat-minus chart and the positive-height support is known
to be on the outgoing forward-tube sheet.

## Finite Flat-Boundary Selector

This is the only remaining hard mathematical body.  It is a finite induction
over flat translated-boundary integrals, not over the live moving source tests.
Do not introduce a chain wrapper for it.  Inside `hflatOrd_selected` and again
inside `hflatAdj_selected`, construct the following values as local `let`s and
`have`s, with the ordinary and raw-adjacent instantiations listed below.

```lean
let Z := Fin n -> Fin (d + 1) -> Complex
let X := BHW.OS45FlatCommonChartReal d n

-- One localized compact piece.  The finite partition construction below
-- supplies `psiF`, `psiZD`, and the equality of the finite sum with the
-- original `psi0Flat` / `D.toZeroDiagonalCLM 1 phi`.
let psiF : SchwartzMap X Complex := psiPieceFlat a
let psiZD : ZeroDiagonalSchwartz d n := psiPieceZD a
let psiS : SchwartzNPoint d n := psiZD.1
let Lpiece : Complex := OS.S n psiZD

have hpsiF_compact : HasCompactSupport (psiF : X -> Complex) := by
  -- `psiF` is `χ a * psi0Flat`; use compact support of `χ a`.

have hpsiF_Uloc :
    tsupport (psiF : X -> Complex) ⊆ Uloc a := by
  -- `tsupport (χ a) ⊆ Uloc a` and support of a product is contained in the
  -- support of the partition factor.

let len : Nat := chainLen
let chart : Fin (len + 1) -> PointedMetricBranchChart Z Complex :=
  chainChart
let edge :
    ∀ j : Fin len,
      PointedSeedEdge
        ((chart (Fin.castSucc j)).center)
        ((chart (Fin.castSucc j)).carrier)
        ((chart (Fin.succ j)).carrier)
        ((chart (Fin.castSucc j)).branch)
        ((chart (Fin.succ j)).branch) :=
  chainEdge

let approach : Fin (len + 1) -> Real -> X -> Z := chainApproach
let weight : Fin (len + 1) -> Real -> SchwartzMap X Complex := chainWeight

let I (j : Fin (len + 1)) (eps : Real) : Complex :=
  ∫ x : X, (chart j).branch (approach j eps x) * (weight j eps x)
```

The displayed names `chainLen`, `chainChart`, `chainEdge`,
`chainApproach`, and `chainWeight` are not new constants.  They stand for the
local objects produced in the current proof block by the existing checked
ordinary or retained raw-adjacent chart constructors.  If Lean needs a helper,
the only acceptable split is a neutral finite-induction lemma for functions
`I : Fin (len + 1) -> Real -> Complex`; the branch corridors, base OS-I
normalizations, and terminal sheet rewrites must remain in the producer body.

### Compact Localization Layer

The local selector above is not run once on the whole compact support unless a
single corridor has already been proved to contain that whole support.  In the
current Hdiff producer, use finite localization.  This is the missing
compact-support step that makes the chart-local collars honest.

```lean
let K0 : Set X := tsupport (psi0Flat : X -> Complex)

have hK0_compact : IsCompact K0 := by
  simpa [K0] using hpsi0Flat_compact.isCompact

-- For every support point choose a local source point and two one-branch
-- corridors, one ordinary and one retained raw-adjacent.
have hlocal_cover_data :
    ∀ y : K0,
      ∃ V : Set X,
        IsOpen V ∧ y.1 ∈ V ∧
        (∃ c R, V ⊆ Metric.closedBall c R) ∧
        V ⊆ BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) ∧
        e.symm '' V ⊆ Usrc := by
  intro y
  let u : NPointDomain d n := e.symm y.1
  have huU : u ∈ Usrc := by
    -- from the source-window support packet for `psi0Flat`.
  have huV : u ∈ P.V := hU_sub (hKsrcU (hUsrc_sub_Ksrc huU))
  -- Build the ordinary corridor along `gammaOrd u`.
  -- Build the retained raw corridor along
  -- `gammaAdjSeed u t = BHW.permAct (d := d) P.τ (gammaOrd u t)`.
  -- Intersect the finitely many zero-height carrier preimages and shrink to a
  -- metric ball in `X`; openness gives side-height collars for small eps.
  -- The actual chart/corridor values are constructed later for each selected
  -- finite cover element, not stored in a public structure.

obtain ⟨s, hs_cover⟩ :=
  hK0_compact.elim_finite_subcover
    (fun y : K0 => Classical.choose (hlocal_cover_data y))
    (fun y : K0 =>
      (Classical.choose_spec (hlocal_cover_data y)).1)
    (fun y : K0 =>
      (Classical.choose_spec (hlocal_cover_data y)).2.1)

let α := { y : K0 // y ∈ s }
let Uloc : α -> Set X := fun a =>
  Classical.choose (hlocal_cover_data a.1)

have hUloc_open : ∀ a : α, IsOpen (Uloc a) := by
  intro a
  exact (Classical.choose_spec (hlocal_cover_data a.1)).1

have hUloc_relcompact : ∀ a : α, ∃ c R, Uloc a ⊆ Metric.closedBall c R := by
  intro a
  exact (Classical.choose_spec (hlocal_cover_data a.1)).2.2.1

have hcover_K0 : K0 ⊆ ⋃ a : α, Uloc a := by
  -- unpack `hs_cover`.

obtain ⟨χ, hχ_compact, hχ_sub, hχ_sum⟩ :=
  SCV.exists_finite_schwartz_partitionOfUnity_on_compact
    hK0_compact hUloc_open hUloc_relcompact hcover_K0

let psiPieceFlat (a : α) : SchwartzMap X Complex :=
  SchwartzMap.smulLeftCLM Complex (χ a : X -> Complex) psi0Flat

have hpsiFlat_sum :
    psi0Flat = ∑ a : α, psiPieceFlat a := by
  simpa [psiPieceFlat] using
    SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
      (Finset.univ : Finset α) χ psi0Flat
      (by
        intro x hx
        simpa using hχ_sum x hx)

let psiPieceSource (a : α) : SchwartzNPoint d n :=
  pullFlatToSource (psiPieceFlat a)

have hpsiPieceSource_zd :
    ∀ a : α, VanishesToInfiniteOrderOnCoincidence (psiPieceSource a) := by
  intro a
  -- Rewrite `psiPieceSource a` as
  -- `SchwartzMap.smulLeftCLM Complex (χ a ∘ e) psi0`, then use the neutral
  -- zero-diagonal multiplication lemma
  -- `VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint`.
  -- This lemma currently exists privately in K2-density files; for this
  -- producer either reprove it locally in the Hdiff file or move the same
  -- statement to a neutral zero-diagonal support file.  It has no OS45,
  -- Wadj, Hdiff, or theorem-2 content.

let psiPieceZD (a : α) : ZeroDiagonalSchwartz d n :=
  ⟨psiPieceSource a, hpsiPieceSource_zd a⟩

have hpsiZD_sum :
    (∑ a : α, psiPieceZD a) =
      D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi := by
  apply Subtype.ext
  change
    (∑ a : α, psiPieceSource a) =
      (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) phi).1
  calc
    (∑ a : α, psiPieceSource a)
        = pullFlatToSource (∑ a : α, psiPieceFlat a) := by
          simp [psiPieceSource, map_sum]
    _ = pullFlatToSource psi0Flat := by rw [← hpsiFlat_sum]
    _ = psi0 := hpull_psi0Flat
```

For each `a : α`, run the local finite selector below with
`psiF := psiPieceFlat a`, `psiS := psiPieceZD a`.1, and
`Lpiece := OS.S n (psiPieceZD a)`.  The global selected flat limit is the
finite sum:

```lean
let psiPieceFlatOrd (a : α) (eps : Real) : SchwartzMap X Complex :=
  SCV.translateSchwartz (-(eps • eta0)) (psiPieceFlat a)

let FlatOrdPiece (a : α) : Real -> Complex := fun eps =>
  ∫ x : X,
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n))
      (fun q => (x q : Complex) + ((eps • eta0) q : Complex) * Complex.I) *
    psiPieceFlatOrd a eps x

let psiPieceFlatAdj (a : α) (eps : Real) : SchwartzMap X Complex :=
  SCV.translateSchwartz (-((-eps) • eta0)) (psiPieceFlat a)

let FlatAdjPiece (a : α) : Real -> Complex := fun eps =>
  ∫ x : X,
    BHW.os45FlatCommonChartBranch d n OS lgc sigmaAdj
      (fun q =>
        (x q : Complex) + (((-1 : Real) * eps) • eta0 q : Complex) *
          Complex.I) *
    psiPieceFlatAdj a eps x

have hflatOrd_piece :
    ∀ a : α, Tendsto (FlatOrdPiece a) l
      (nhds (J * OS.S n (psiPieceZD a))) := by
  intro a
  -- local ordinary selector below

have hFlatOrd_sum :
    ∀ᶠ eps in l, FlatOrd eps = ∑ a : α, FlatOrdPiece a eps := by
  -- Use `hpsiFlat_sum`, linearity of `SCV.translateSchwartzCLM`, and
  -- `integral_finset_sum`.

have hflatOrd_selected :
    Tendsto FlatOrd l (nhds (J * Lcur)) := by
  have hsum_piece :
      Tendsto (fun eps : Real => ∑ a : α, FlatOrdPiece a eps) l
        (nhds (∑ a : α, J * OS.S n (psiPieceZD a))) :=
    tendsto_finset_sum (fun a _ => hflatOrd_piece a)
  have hlimit :
      (∑ a : α, J * OS.S n (psiPieceZD a)) = J * Lcur := by
    calc
      (∑ a : α, J * OS.S n (psiPieceZD a))
          = J * OS.S n (∑ a : α, psiPieceZD a) := by
            simp [Finset.mul_sum, (OS.E0_linear n).map_sum]
      _ = J * Lcur := by
            simp [Lcur, hpsiZD_sum]
  have hsum_global :
      Tendsto (fun eps : Real => ∑ a : α, FlatOrdPiece a eps)
        l (nhds (J * Lcur)) := by
    simpa [hlimit] using hsum_piece
  exact hsum_global.congr' hFlatOrd_sum.symm

have hflatAdj_piece :
    ∀ a : α, Tendsto (FlatAdjPiece a) l
      (nhds (J * OS.S n (psiPieceZD a))) := by
  intro a
  -- local retained raw-adjacent selector below

have hFlatAdj_sum :
    ∀ᶠ eps in l, FlatAdj eps = ∑ a : α, FlatAdjPiece a eps := by
  -- Same finite-sum proof as the ordinary side, with
  -- `SCV.translateSchwartzCLM (-((-eps) • eta0))`.

have hflatAdj_selected :
    Tendsto FlatAdj l (nhds (J * Lcur)) := by
  have hsum_piece :
      Tendsto (fun eps : Real => ∑ a : α, FlatAdjPiece a eps) l
        (nhds (∑ a : α, J * OS.S n (psiPieceZD a))) :=
    tendsto_finset_sum (fun a _ => hflatAdj_piece a)
  have hlimit :
      (∑ a : α, J * OS.S n (psiPieceZD a)) = J * Lcur := by
    calc
      (∑ a : α, J * OS.S n (psiPieceZD a))
          = J * OS.S n (∑ a : α, psiPieceZD a) := by
            simp [Finset.mul_sum, (OS.E0_linear n).map_sum]
      _ = J * Lcur := by
            simp [Lcur, hpsiZD_sum]
  have hsum_global :
      Tendsto (fun eps : Real => ∑ a : α, FlatAdjPiece a eps)
        l (nhds (J * Lcur)) := by
    simpa [hlimit] using hsum_piece
  exact hsum_global.congr' hFlatAdj_sum.symm
```

For each adjacent piece, the raw `(4.12)` base value is normalized to
`OS.S n (psiPieceZD a)` by `bvt_euclidean_restriction` plus
`OS.E3_symmetric`, not by the special current-test theorem for the unsplit
`D.toZeroDiagonalCLM` test.

### Per-Piece Corridor Construction

For each selected finite-cover index `a : α`, reconstruct the one-branch
corridor locally.  Do not store a public corridor object; use a proof-local
reachability predicate whose witnesses are exactly the values consumed by the
local selector.

```lean
let ya : K0 := a.1
let ua : NPointDomain d n := e.symm ya.1

have hua : ua ∈ Usrc := by
  -- from `hcover_K0`, `hpsiF_Uloc`, and the chosen local source window.

have huaV : ua ∈ P.V := hU_sub (hKsrcU (hUsrc_sub_Ksrc hua))

let gammaOrd_a : unitInterval -> Z :=
  BHW.os45Figure24IdentityPath (d := d) (n := n) ua

let gammaAdj_a : unitInterval -> Z :=
  fun t => BHW.permAct (d := d) P.τ (gammaOrd_a t)
```

Ordinary reachability:

```lean
let ReachOrd : Set unitInterval := {t |
  ∃ len : Nat,
  ∃ chart : Fin (len + 1) -> PointedMetricBranchChart Z Complex,
  ∃ edge :
      ∀ j : Fin len,
        PointedSeedEdge
          ((chart (Fin.castSucc j)).center)
          ((chart (Fin.castSucc j)).carrier)
          ((chart (Fin.succ j)).carrier)
          ((chart (Fin.castSucc j)).branch)
          ((chart (Fin.succ j)).branch),
    (chart 0).center = gammaOrd_a 0 ∧
    (chart (Fin.last len)).center = gammaOrd_a t ∧
    (∀ j, OrdModelAtZ0 d n ((chart j).center)
      (BHW.extendF (bvt_F OS lgc n)) (chart j)) }

have hReachOrd0 : (0 : unitInterval) ∈ ReachOrd := by
  -- Use `H.ordinaryWick_pointedChartInWindow` at `ua`.

have hReachOrd_local :
    ∀ t : unitInterval, ∃ U : Set unitInterval, IsOpen U ∧ t ∈ U ∧
      ∀ ⦃s r : unitInterval⦄,
        s ∈ U -> r ∈ U -> s ∈ ReachOrd -> r ∈ ReachOrd := by
  intro t
  -- Build endpoint-centered ordinary charts by
  -- `H.ordinaryCommonEdge_pointedChartInWindow` or the ordinary Wick/window
  -- adapter appropriate to `gammaOrd_a t`.
  -- The successor edge is `pointed_seed_edge_of_common_model`, then
  -- the support collars are shrunk later using `hpsiF_Uloc`.

have hReachOrd_all : ReachOrd = Set.univ :=
  SCV.reachable_eq_univ_of_local_symmetric_extension
    ⟨0, hReachOrd0⟩ hReachOrd_local

obtain ⟨lenOrd, chartOrd, edgeOrd, hstartOrd, hendOrd, hmodelOrd⟩ :
    ∃ len : Nat,
    ∃ chart : Fin (len + 1) -> PointedMetricBranchChart Z Complex,
    ∃ edge :
      ∀ j : Fin len,
        PointedSeedEdge
          ((chart (Fin.castSucc j)).center)
          ((chart (Fin.castSucc j)).carrier)
          ((chart (Fin.succ j)).carrier)
          ((chart (Fin.castSucc j)).branch)
          ((chart (Fin.succ j)).branch),
      (chart 0).center = gammaOrd_a 0 ∧
      (chart (Fin.last len)).center = gammaOrd_a 1 ∧
      (∀ j, OrdModelAtZ0 d n ((chart j).center)
        (BHW.extendF (bvt_F OS lgc n)) (chart j)) := by
  have hterminal : (1 : unitInterval) ∈ ReachOrd := by
    simpa [hReachOrd_all]
  simpa [ReachOrd] using hterminal
```

Raw-adjacent reachability is the same shape with `gammaAdj_a`, but every chart
keeps retained raw `(4.12)` provenance.

```lean
let ReachAdj : Set unitInterval := {t |
  ∃ len : Nat,
  ∃ chart : Fin (len + 1) -> PointedMetricBranchChart Z Complex,
  ∃ edge :
      ∀ j : Fin len,
        PointedSeedEdge
          ((chart (Fin.castSucc j)).center)
          ((chart (Fin.castSucc j)).carrier)
          ((chart (Fin.succ j)).carrier)
          ((chart (Fin.castSucc j)).branch)
          ((chart (Fin.succ j)).branch),
    (chart 0).center = gammaAdj_a 0 ∧
    (chart (Fin.last len)).center = gammaAdj_a 1 ∧
    (∀ j : Fin (len + 1),
      ∃ rawLocal : PointedMetricBranchChart Z Complex,
        RawRetargetAtZ0 d n ((chart j).center) (chart j) rawLocal) }
```

The raw local propagation input uses `H.OS412SeedWindow_pointedChart`,
`RawRetargetAtZ0.edge_to_raw`, and, when two raw restrictions must be compared,
`os45_pointed_gallery_pair_one_one`.  It does not use
`LocalOverlapAtZ0.flat_plus_minus`, `LocalOverlapAtZ0.flat_minus_plus`, or
`localOverlapAtZ0_galleryPair`.

The support contracts are deliberately not fields of `ReachOrd` or `ReachAdj`.
After the terminal chain is obtained, prove the edge and terminal collar
membership directly from `hpsiF_Uloc`, the open carrier balls, and continuity of
the concrete `approach` used in that edge.  If Lean requires a named helper
here, make it a neutral finite-reachability lemma over arbitrary charts and
edges; do not add an OS45 source-current wrapper.

The ordinary instantiation is:

```lean
-- chart 0: ordinary `(4.1)` incoming chart.
-- carrier is inside `(BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W`.
-- branch is `BHW.extendF (bvt_F OS lgc n)` on the carrier.
obtain ⟨A0, hA0_center, hA0_mem, hA0_sub, hA0_model, hA0_trace⟩ :=
  H.ordinaryWick_pointedChartInWindow OS lgc hbase_u_mem
    hbaseW_open hbaseW_mem

-- terminal chart: ordinary common-edge flat-plus chart.
-- branch is still `BHW.extendF (bvt_F OS lgc n)` on the carrier.
obtain
    ⟨Aterm, hAterm_center, hAterm_mem, hAterm_sub,
      hAterm_model, hAterm_trace⟩ :=
  H.ordinaryCommonEdge_pointedChartInWindow hd OS lgc hterminal_u_mem
    hterminalW_open hterminalW_mem

have hordinary_edge :
    ∀ j : Fin len,
      PointedSeedEdge
        ((chart (Fin.castSucc j)).center)
        ((chart (Fin.castSucc j)).carrier)
        ((chart (Fin.succ j)).carrier)
        ((chart (Fin.castSucc j)).branch)
        ((chart (Fin.succ j)).branch) := by
  intro j
  exact pointed_seed_edge_of_common_model
    (chart (Fin.castSucc j)).carrier_open
    (chart (Fin.succ j)).carrier_open
    hleftOrd.z0_mem hrightOrd.z0_mem
    hleftOrd.eq_ord hrightOrd.eq_ord
```

The ordinary base limit is not derived from the terminal side lift.  It is the
genuine fixed `(4.1)` boundary-value theorem after the already checked CLE/test
pullback:

```lean
have hbaseOrd_coord :
    ∀ᶠ eps in l,
      I 0 eps =
        J * (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (fun k μ =>
              (u k μ : Complex) +
                (eps : Complex) * (etaOrd k μ : Complex) * Complex.I) *
          (psiS : NPointDomain d n -> Complex) u) := by
  -- Expand the first chart's local approach and `weight 0`.
  -- Use the fixed CLE/test pullback, `hpull_psi0Flat`, and the Jacobian
  -- formula for `BHW.os45CommonEdgeFlatCLE`.
  -- The proof must also establish the small-positive carrier membership in
  -- the incoming ordinary window on the support of `weight 0 eps`.

have hetaOrd : InForwardCone d n etaOrd := by
  -- This is the checked incoming `(4.1)` direction attached to the first
  -- ordinary chart.  It is not manufactured from terminal `eta0`.

have hbaseOrd_raw :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (fun k μ =>
              (u k μ : Complex) +
                (eps : Complex) * (etaOrd k μ : Complex) * Complex.I) *
          (psiS : NPointDomain d n -> Complex) u)
      l (nhds Lpiece) := by
  have h41 :=
    ordinary41_fixed_test_boundaryValue_extendF OS lgc psiS etaOrd hetaOrd
  have hWick :
      bvt_W OS lgc n psiS = Lpiece := by
    simpa [Lpiece, psiS] using
      (bvt_euclidean_restriction (d := d) OS lgc n
        psiZD).symm
  simpa [hWick] using h41

have hbase :
    Tendsto (fun eps : Real => I 0 eps) l (nhds (J * Lpiece)) := by
  exact (hbaseOrd_raw.const_mul J).congr' hbaseOrd_coord.symm
```

The raw-adjacent instantiation is parallel but has a different incoming sheet:

```lean
-- chart 0: retained raw `(4.12)` seed at `gammaAdjSeed 0`.
obtain ⟨A0, hA0_center, hA0_mem, hA0_sub, hA0_model, hA0_trace⟩ :=
  H.OS412SeedWindow_pointedChart OS lgc hbase_u_mem

-- Incoming domain and branch:
--   A0.carrier <=
--     (({z | BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) ∩
--       (BHW.ExtendedTube d n ∩
--         BHW.permutedExtendedTubeSector d n P.τ))
--   Set.EqOn A0.branch BSeed412 A0.carrier
-- where `BSeed412 z = bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)`.

have hraw_edges :
    ∀ j : Fin len,
      PointedSeedEdge
        ((chart (Fin.castSucc j)).center)
        ((chart (Fin.castSucc j)).carrier)
        ((chart (Fin.succ j)).carrier)
        ((chart (Fin.castSucc j)).branch)
        ((chart (Fin.succ j)).branch) := by
  intro j
  -- Interior raw steps use `RawRetargetAtZ0.edge_to_raw`, or two such
  -- retargeting steps compared by `os45_pointed_gallery_pair_one_one`.
  -- No `LocalOverlapAtZ0.flat_plus_minus` or `.flat_minus_plus` call is in
  -- scope here.
  exact hretainedRawEdge j

have hbaseAdj_coord :
    ∀ᶠ eps in l,
      I 0 eps =
        J * (∫ u : NPointDomain d n,
          bvt_F OS lgc n
            (BHW.permAct (d := d) P.τ
              (fun k μ =>
                (u k μ : Complex) +
                  (eps : Complex) * (etaAdj k μ : Complex) * Complex.I)) *
          (psiS : NPointDomain d n -> Complex) u) := by
  -- Expand the raw first chart, use `hA0_model`, the fixed CLE/test
  -- pullback, and the same Jacobian formula.

have hetaAdj :
    (fun k μ => etaAdj (P.τ k) μ) ∈ ForwardConeAbs d n := by
  -- This is the checked retained raw `(4.12)` incoming direction.
  -- It is local to the raw seed chart and is not inferred from `eta0`.

have hbaseAdj_raw :
    Tendsto
      (fun eps : Real =>
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n
            (BHW.permAct (d := d) P.τ
              (fun k μ =>
                (u k μ : Complex) +
                  (eps : Complex) * (etaAdj k μ : Complex) * Complex.I)) *
          (psiS : NPointDomain d n -> Complex) u)
      l (nhds Lpiece) := by
  have h412 :=
    raw412_fixed_test_boundaryValue OS lgc P.τ psiS etaAdj hetaAdj
  have h412_value :
      bvt_W OS lgc n (BHW.permuteSchwartz (d := d) P.τ.symm psiS) =
        Lpiece := by
    -- Use `bvt_euclidean_restriction` for the permuted zero-diagonal test,
    -- then `OS.E3_symmetric` to identify the permuted Schwinger value with
    -- `OS.S n psiZD`.
  simpa [h412_value] using h412

have hbase :
    Tendsto (fun eps : Real => I 0 eps) l (nhds (J * Lpiece)) := by
  exact (hbaseAdj_raw.const_mul J).congr' hbaseAdj_coord.symm
```

The terminal contract is also local.  In the ordinary selector,
`chart (Fin.last len)` has the ordinary common-edge model
`BHW.extendF (bvt_F OS lgc n)`.  In the raw-adjacent selector,
`chart (Fin.last len)` is still reached through retained raw provenance; on the
eventual positive-height terminal support one first proves

```lean
have hterminalAdj_sheet :
    ∀ᶠ eps in l, ∀ x,
      x ∈ Function.support (psiFlatAdj eps : X -> Complex) ->
        BHW.permAct (d := d) P.τ
          (sideLift (-1 : Real) eps eta0 x) ∈ BHW.ForwardTube d n := by
  -- This is the terminal support-local sheet membership from the side
  -- support radius and the retained raw terminal chart.  It is not an
  -- incoming seed hypothesis.
```

Then `BHW.extendF_eq_on_forwardTube` rewrites the raw terminal branch to the
displayed `extendF (bvt_F OS lgc n) (BHW.permAct P.τ z)` form used by the
source-side DCT.

The terminal approach has a concrete form.  Define it locally; use it only for
the terminal chart and terminal normal-form rewrites unless the current edge's
approach contract has already been proved to be this expression.

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

let psiFlatOrd (eps : Real) :=
  SCV.translateSchwartz (-(eps • eta0)) psiF

let psiFlatAdj (eps : Real) :=
  SCV.translateSchwartz (-((-eps) • eta0)) psiF
```

The compact-collar proof used at the terminal chart and at any edge with a
known chart-local approach is always the same pattern:

```lean
have hterminal_collar :
    ∀ᶠ eps in l, ∀ x,
      x ∈ Function.support
          (psiFlatOrd eps : BHW.OS45FlatCommonChartReal d n -> Complex) ->
        sideLift (1 : Real) eps eta0 x ∈ terminalCarrier := by
  let Kpiece : Set (BHW.OS45FlatCommonChartReal d n) :=
    tsupport (psiF :
      BHW.OS45FlatCommonChartReal d n -> Complex)
  have hKpiece : IsCompact Kpiece := by
    simpa [Kpiece] using hpsiF_compact.isCompact
  have hlocal :
      ∀ y : Kpiece, ∀ᶠ eps in nhds (0 : Real),
        sideLift (1 : Real) eps eta0 (y.1 + eps • eta0) ∈
          terminalCarrier := by
    intro y
    have hy0 : sideLift (1 : Real) 0 eta0 y.1 ∈ terminalCarrier :=
      hterminal_zero_tsupport y.1 y.2
    have hcont :
        ContinuousAt
          (fun p : Real × BHW.OS45FlatCommonChartReal d n =>
            sideLift (1 : Real) p.1 eta0 (p.2 + p.1 • eta0))
          ((0 : Real), y.1) := by
      -- continuity of `os45QuarterTurnCLE.symm`, `unflattenCfg`, and
      -- coordinatewise algebra in `flatSide`.
      fun_prop
    have hpath :
        Tendsto (fun eps : Real => (eps, y.1))
          (nhds (0 : Real)) (nhds ((0 : Real), y.1)) := by
      simpa using tendsto_id.prod_mk tendsto_const_nhds
    exact (hcont.tendsto.comp hpath).eventually
      (terminalCarrier_open.mem_nhds hy0)
  have hall :
      ∀ᶠ eps in nhds (0 : Real), ∀ y ∈ Kpiece,
        sideLift (1 : Real) eps eta0 (y + eps • eta0) ∈
          terminalCarrier := by
    simpa [Kpiece] using
      hKpiece.eventually_forall_of_forall_eventually hlocal
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds] with eps heps x hx
  let y := x - eps • eta0
  have hy_support :
      y ∈ Function.support
        (psiF : BHW.OS45FlatCommonChartReal d n -> Complex) := by
    have hx_translate :
        x ∈ Function.support
          (SCV.translateSchwartz (-(eps • eta0)) psiF :
            BHW.OS45FlatCommonChartReal d n -> Complex) := by
      simpa [psiFlatOrd] using hx
    have hy' :=
      (SCV.mem_support_translateSchwartz_iff
        (-(eps • eta0)) psiF x).mp hx_translate
    simpa [y, sub_eq_add_neg] using hy'
  have hyK : y ∈ Kpiece := subset_tsupport _ hy_support
  have hx_eq : y + eps • eta0 = x := by
    simp [y, sub_eq_add_neg, add_assoc]
  simpa [hx_eq] using heps y hyK
```

For the adjacent terminal collar replace `1` by `-1`, `eps • eta0` by
`(-eps) • eta0`, and `psiFlatOrd` by `psiFlatAdj`.

For each edge `j : Fin len`, first put both adjacent chart integrals into the
same local edge coordinates.  This is where any CLE/test pullback or
coordinate-change calculation for that edge is discharged; do not hide it in a
new branch packet.

```lean
let A := chart (Fin.castSucc j)
let B := chart (Fin.succ j)
let step := edge j

let edgeApproach : Real -> X -> Z := approach (Fin.castSucc j)
let edgeWeight : Real -> SchwartzMap X Complex := weight (Fin.castSucc j)

have hleft_to_edge :
    ∀ᶠ eps in l,
      I (Fin.castSucc j) eps =
        ∫ x : X, A.branch (edgeApproach eps x) * edgeWeight eps x := by
  -- Usually `rfl`; if the left chart uses a local CLE coordinate, expand that
  -- coordinate here and use the checked pullback equality for the fixed test.

have hright_to_edge :
    ∀ᶠ eps in l,
      I (Fin.succ j) eps =
        ∫ x : X, B.branch (edgeApproach eps x) * edgeWeight eps x := by
  -- This is the edge-local coordinate contract.  On the fixed translated
  -- support it proves that the right chart is being evaluated at the same
  -- `edgeApproach eps x` and with the same `edgeWeight eps`; off the support
  -- both sides are zero by `Function.mem_support`.

have hEq_inter :
    Set.EqOn A.branch B.branch (A.carrier ∩ B.carrier) :=
  PointedMetricBranchChart.eqOn_inter_of_seed A B
    ⟨step.W, step.W_open, step.z0_mem, step.W_sub, step.eqOn⟩

have hedge_collar :
    ∀ᶠ eps in l, ∀ x,
      x ∈ Function.support
          (edgeWeight eps : X -> Complex) ->
        edgeApproach eps x ∈ A.carrier ∩ B.carrier := by
  -- compactness of `tsupport psiF`, the support behavior of
  -- `SCV.translateSchwartz`, continuity of the edge-local approach, and the
  -- open metric-ball carriers.

have hedge_same_coordinates :
    ∀ᶠ eps in l,
      (∫ x : X, A.branch (edgeApproach eps x) * edgeWeight eps x) =
      (∫ x : X, B.branch (edgeApproach eps x) * edgeWeight eps x) := by
  filter_upwards [hedge_collar] with eps hmem
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx :
      x ∈ Function.support
        (edgeWeight eps : X -> Complex)
  · exact by
      have hz := hmem x hx
      simp [hEq_inter hz]
  · have hzero : edgeWeight eps x = 0 := by
      exact not_ne_iff.mp (by simpa [Function.mem_support] using hx)
    simp [hzero]

have hedge_integral_eq :
    ∀ᶠ eps in l,
      I (Fin.castSucc j) eps = I (Fin.succ j) eps := by
  filter_upwards
    [hleft_to_edge, hright_to_edge, hedge_same_coordinates]
    with eps hleft hright hsame
  exact hleft.trans (hsame.trans hright.symm)
```

The finite induction transports the fixed boundary limit from chart `j` to
`j + 1` by `Tendsto.congr' hedge_integral_eq`.  This is where the identity
theorem is used.  A proof that only stores a small seed neighborhood and never
calls `PointedMetricBranchChart.eqOn_inter_of_seed` is incomplete.

The local induction should be written directly:

```lean
have hstep :
    ∀ j : Fin len,
      ∀ᶠ eps in l, I (Fin.castSucc j) eps = I (Fin.succ j) eps := by
  intro j
  -- inline the edge proof displayed above for this `j`.

have hchain :
    ∀ m : Nat, ∀ hm : m ≤ len,
      Tendsto
        (fun eps : Real => I ⟨m, Nat.lt_succ_of_le hm⟩ eps)
        l (nhds (J * Lpiece)) := by
  intro m hm
  induction m with
  | zero =>
      simpa using hbase
  | succ m ih =>
      have hm_le_len : m ≤ len := Nat.le_trans (Nat.le_succ m) hm
      have hm_lt_len : m < len := Nat.lt_of_succ_le hm
      let j : Fin len := ⟨m, hm_lt_len⟩
      have hprev :
          Tendsto
            (fun eps : Real => I (Fin.castSucc j) eps)
            l (nhds (J * Lpiece)) := by
        simpa [j] using ih hm_le_len
      exact hprev.congr' (hstep j)

have hlast :
    Tendsto (fun eps : Real => I (Fin.last len) eps)
      l (nhds (J * Lpiece)) := by
  simpa using hchain len le_rfl
```

After the finite induction reaches the terminal chart, prove the two terminal
normal forms before scalar cancellation:

```lean
let terminal := chart (Fin.last len)

have hterminal_slot_ord :
    ∀ᶠ eps in l,
      I (Fin.last len) eps =
        ∫ x : X,
          terminal.branch (sideLift (1 : Real) eps eta0 x) *
            psiFlatOrd eps x := by
  -- Expand `approach (Fin.last len)` and `weight (Fin.last len)`.
  -- This is the terminal chart's own local-data contract.

have hterminalOrd_model :
    Set.EqOn terminal.branch (BHW.extendF (bvt_F OS lgc n))
      terminal.carrier := by
  -- Ordinary terminal chart comes from
  -- `H.ordinaryCommonEdge_pointedChartInWindow`; use its `eq_ord` field.

have hterminal_to_flat_ord :
    ∀ᶠ eps in l,
      I (Fin.last len) eps = FlatOrdPiece a eps := by
  filter_upwards [hterminal_slot_ord, hterminal_collar_ord]
    with eps hslot hmem
  refine hslot.trans ?_
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx :
      x ∈ Function.support
        (psiFlatOrd eps : X -> Complex)
  · have hz := hmem x hx
    have hmodel :
        terminal.branch (sideLift (1 : Real) eps eta0 x) =
          BHW.extendF (bvt_F OS lgc n)
            (sideLift (1 : Real) eps eta0 x) :=
      hterminalOrd_model hz
    simp [FlatOrdPiece, sideLift, flatSide,
      BHW.os45FlatCommonChartBranch, BHW.os45PulledRealBranch, hmodel]
  · have hzero : psiFlatOrd eps x = 0 := by
      exact not_ne_iff.mp (by simpa [Function.mem_support] using hx)
    simp [hzero]

have hterminal_slot_adj :
    ∀ᶠ eps in l,
      I (Fin.last len) eps =
        ∫ x : X,
          terminal.branch (sideLift (-1 : Real) eps eta0 x) *
            psiFlatAdj eps x := by
  -- Expand the raw terminal chart's approach and translated test.

have hterminalAdj_raw_model :
    Set.EqOn terminal.branch BSeed412 terminal.carrier := by
  -- This is retained raw `(4.12)` provenance transported to the terminal
  -- chart by the finite raw corridor.

have hterminal_to_flat_adj :
    ∀ᶠ eps in l,
      I (Fin.last len) eps = FlatAdjPiece a eps := by
  filter_upwards
    [hterminal_slot_adj, hterminal_collar_adj, hterminalAdj_sheet]
    with eps hslot hmem hsheet
  refine hslot.trans ?_
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx :
      x ∈ Function.support
        (psiFlatAdj eps : X -> Complex)
  · have hz := hmem x hx
    have hraw :
        terminal.branch (sideLift (-1 : Real) eps eta0 x) =
          bvt_F OS lgc n
            (BHW.permAct (d := d) P.τ
              (sideLift (-1 : Real) eps eta0 x)) := by
      simpa [BSeed412] using hterminalAdj_raw_model hz
    have hF_eq :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (sideLift (-1 : Real) eps eta0 x)) =
          bvt_F OS lgc n
            (BHW.permAct (d := d) P.τ
              (sideLift (-1 : Real) eps eta0 x)) := by
      exact BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
        hF_holo hF_real_inv
        _ (hsheet x hx)
    have hmodel :
        terminal.branch (sideLift (-1 : Real) eps eta0 x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (sideLift (-1 : Real) eps eta0 x)) :=
      hraw.trans hF_eq.symm
    have hSigmaAdj_symm : sigmaAdj.symm = P.τ := by
      simp [sigmaAdj]
    simp [FlatAdjPiece, sideLift, flatSide,
      BHW.os45FlatCommonChartBranch, BHW.os45PulledRealBranch,
      hmodel, hSigmaAdj_symm]
  · have hzero : psiFlatAdj eps x = 0 := by
      exact not_ne_iff.mp (by simpa [Function.mem_support] using hx)
    simp [hzero]
```

The selected fixed flat limits are then:

```lean
have hflatOrd_piece_a :
    Tendsto (FlatOrdPiece a) l (nhds (J * Lpiece)) :=
  hlast.congr' hterminal_to_flat_ord

have hflatAdj_piece_a :
    Tendsto (FlatAdjPiece a) l (nhds (J * Lpiece)) :=
  hlast.congr' hterminal_to_flat_adj
```

## Moving Test Status

The live goals contain moving side tests, but the active proof does not
transport those moving tests through the chart chain.  The fixed endpoint value
is selected first; then the checked moving endpoint DCT already present in the
Hdiff body changes the moving tests to the same endpoint.

Use the concrete Figure-2-4 cutoff facts for the moving endpoint DCT:

```lean
D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually
D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero
BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
```

These facts take the original flat test `phi` and the source-window packet
`hφUsrc`; do not feed `psi0Flat` to them.  The auxiliary `psi0Flat` belongs
only to the fixed scalar-cancellation selector.

## Implementation Order

1. In `hOrd_side_current`, define `psi0Flat`, `OrdFixed`, and `OrdEndpoint`.
   Prove `hOrd_fixed_selected` by expanding the ordinary fixed flat selector;
   prove `hOrd_fixed_endpoint`; rewrite the existing `hOrd_endpoint_DCT`.
2. In `hAdj_side_current`, define `sigmaAdj`, `tauOut`, `AdjFixed`, and
   `AdjEndpoint`.  Prove `hAdj_fixed_selected` from the retained raw `(4.12)`
   fixed flat selector; prove `hAdj_fixed_endpoint`; rewrite the existing
   `hAdj_endpoint_DCT`.
3. Only after both moving current limits are closed may the downstream flat EOW
   seed, local common-boundary CLM, local `S'_n`, pair carrier, and later
   theorem-2 wrapper work resume.

## Remaining Proof-Doc Gate

The prior `etaBaseOrd/etaBaseAdj` route is rejected.  The direct
moving-current induction route is also rejected.  The remaining Lean-entry gate
is now the fixed flat translated-boundary selector:

```lean
hflatOrd_selected
hflatAdj_selected
hedge_integral_eq for each chart-local fixed selector edge
hterminal_to_flat_ord
hterminal_to_flat_adj
```

The surrounding fixed endpoint DCT, moving endpoint DCT, scalar cancellation,
inverse-CLE support, and Schwinger normalization facts already have checked
support theorems or local proof scripts in the frontier file.  The hard proof
body is the finite one-branch selector itself.
