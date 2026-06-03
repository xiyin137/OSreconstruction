# Theorem 2 Adjacent Wick Boundary Pairing Leaf Audit

Date: 2026-06-02

This note records the current status of the local OS-I Section 4.5
E-to-R/Theorem-2 route after the Jost/EOW smearing producer was closed.

## Lean Status

File:

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45JostEOWSmearing.lean
```

Fresh exact check:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45JostEOWSmearing.lean
# exits 0
```

Placeholder scan:

```bash
rg -n "\?os45_OSI45|\bsorry\b|\badmit\b|\baxiom\b" \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45JostEOWSmearing.lean
# no matches
```

Downstream checks:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
# exits 0

lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanReducedNormalOS45Bridge.lean
# exits 0
```

## Closed Leaf

The former live leaves

```text
?os45_OSI45_localSPrime_openSeed_from_common_boundary_EOW
?os45_OSI45_sourceCommonEdge_eqOn_seed_neighborhood
```

are gone from `JostEOWSmearing`.

The proof now constructs the compact Figure-2-4 real Jost pairing packet via

```lean
os45_compactFigure24WickPairingEq_of_distributional_locality
```

This helper is not a new input gate.  It applies the checked public theorem

```lean
BHW.extendF_adjSwap_eq_on_realOpen_of_distributional_local_commutativity
```

on `BHW.os45Figure24SourcePatch`, using:

- `bvt_F_holomorphic`
- `bvt_F_restrictedLorentzInvariant_forwardTube`
- `bvt_boundary_values`
- `bvt_locally_commutative`
- source-patch openness, Jost/spacelike membership, and both ET-membership
  lemmas from `OSToWightmanLocalityOS45Figure24`

The compact packet is then consumed by

```lean
BHW.os45CommonEdge_transported_wick_pairing_of_compactFigure24WickPairingEq
```

to produce the deterministic adjacent Wick pairing for the theorem's source
window.  The remaining steps are checked consumers:

```lean
BHW.os45CommonEdge_sourceRepresentsZero_of_initialOverlap_adjacentBranch
BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn
```

## Route Guard

The closed proof does not call the guarded legacy
`localSPrime_twoSectorBranch_of_EOW_BHW` producer, does not introduce an
`S'_n` branch, and does not use selected-data packets or
`OSToWightmanLocalityOS45Figure24Hdiff.lean` as producers.

## Downstream Handoff

`OSToWightmanLocalityOS45Figure24Hdiff.lean` now consumes the closed smearing
producer cleanly.  During the downstream check, obsolete duplicate declarations
were removed:

```lean
BHW.OS45BHWJostHullData.OS412SeedWindow_adjacentModel_permActWick_pairing_eq_ordinaryWick
BHW.os45CommonEdge_localHdiffGerm_of_initialOverlap_adjacentBranch
BHW.os45CommonEdge_sourceRepresentsZero_of_initialOverlap_adjacentBranch
```

The first public theorem already lives in
`OSToWightmanLocalityOS45Figure24Seed.lean`; the latter two already live in
`OSToWightmanLocalityOS45BHWJostLocal.lean`.

`OSToWightmanReducedNormalOS45Bridge.lean` also checks.  Its relevant active
consumer remains

```lean
reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45HdiffGerm_sourceSide_asymptotic
```

which converts support-local OS45 Hdiff/source-side packets into
`ReducedLocalAdjacentBoundaryCLMInvariant`.

The remaining theorem-2 boundary-value placeholder is still

```lean
private theorem bvt_W_swap_pairing_of_spacelike
```

in `OSToWightmanBoundaryValues.lean`.  The checked downstream route from that
point is:

```text
support-local OS45 normal asymptotic packet
  -> ReducedLocalAdjacentBoundaryCLMInvariant
  -> ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
  -> bvt_W_swap_pairing_of_spacelike_from_closedSupportCanonicalInvariant
```

The next honest producer is therefore the support-local packet existence for
each reduced spacelike support point.  In the current theorem surfaces this is
the `hlocal` input to

```lean
reducedLocalAdjacentBoundaryCLMInvariant_of_local_OS45HdiffGerm_sourceSide_asymptotic
```

or equivalently a support-local

```lean
Nonempty
  (LocalEdgePairingOS45NormalAsymptoticBranchPacket
    (d := d) hd OS lgc hi p)
```

producer, with:

- a Figure-2-4 canonical source patch `P` containing the reduced-normal
  representative (`hpP`);
- the local common-edge/Hdiff zero packet from the compact Figure-2-4 pairing;
- the two OS-I `(4.12)`--`(4.14)` source-side asymptotic transfers from the
  moving OS45 source rays to the canonical reduced rays.

Do not close `bvt_W_swap_pairing_of_spacelike` through the legacy selected-data
or `AdjacentReducedRuelleDistributionalLimit` diagnostic surfaces.  Those
routes remain checked comparison infrastructure, but they are not the active
Path-2 theorem producer.

## 2026-06-02 Point-Centered Source-Patch Audit

The current codebase still does not contain a proved constructor turning an
arbitrary reduced spacelike support point

```lean
p : AdjacentNormal.ReducedSpace d m i ⟨i.val + 1, hi⟩
```

into a point-centered

```lean
P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd (m + 1) i hi
```

with

```lean
AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
    (AdjacentNormal.reducedAdjacent_succ_ne i hi)
    ((0 : SpacetimeDim d), p) ∈ P.V
```

The public constructor

```lean
BHW.exists_os45_adjacent_identity_canonicalSourcePatch_with_orientedPath
```

still builds the fixed canonical Figure-2-4 witness patch coming from
`figure24_adjacentTwoPlaneRotationSupport`.  The reduced-normal bridge proves
that a supplied `P` gives an open reduced-normal preimage and the required
ordinary/adjacent real branch-domain membership, but it deliberately assumes
the membership above rather than constructing `P`.

Two nearby checked pieces are useful but insufficient:

- `OSToWightmanReducedOneSpacelikePET.lean` proves the selected spacelike
  one-difference PET boundary leaf.  It does not assemble the frozen spectator
  variables into a many-point mixed-tube/Figure-2-4 source window.
- The cone-height identities in
  `OSToWightmanReducedNormalOS45Bridge.lean` identify reduced differences of
  cone-valid OS45 moving source rays with the canonical reduced rays.  They do
  not replace the OS-I moving-source/quarter-turn mixed-tube transfer that
  produces the source-representation or local edge-pairing packet.

The genuine remaining theorem producer is therefore not another downstream
consumer.  It is the point-centered OS-I Section 4.5 mixed-tube/EOW
construction in reduced frozen-spectator normal coordinates: construct
`AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn` on an open
reduced-normal collar around the support point, then prove the two
`(4.12)`--`(4.14)` source-side asymptotic transfers to the canonical reduced
rays on that collar.  A Figure-2-4 source patch can be used only after proving
the collar is genuinely Jost-localized.

## 2026-06-02 Packet-Strength Correction

The Lean surface now records why the support-local OS45 packet cannot be the
unqualified arbitrary-support theorem-2 producer:

```lean
LocalEdgePairingOS45NormalAsymptoticBranchPacket.zeroCenter_mem_jost
LocalEdgePairingOS45NormalAsymptoticBranchPacket.zeroCenter_pair_spacelike
```

These checked lemmas show that a packet with

```lean
hpP :
  AdjacentNormal.coordInv ... ((0 : SpacetimeDim d), p) ∈ P.V
```

forces the zero-center absolute representative of `p` into the full Jost patch
`P.V`, hence every pair in that representative is spacelike.  The theorem-2
hypothesis supplies only the selected adjacent pair.  Therefore the arbitrary
adjacent-spacelike support producer should target the already checked

```lean
AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn
```

surface directly, using a frozen-spectator mixed-tube/EOW construction on an
open reduced-normal collar `E`.  The OS45 local-edge packet remains a valid
consumer on genuinely Jost-localized collars, but it should no longer be treated
as the general support-local theorem-2 input.

## 2026-06-02 Corrected Final-Mile Entry

The downstream theorem-2 surface is now checked as a single theorem:

```lean
bvt_W_swap_pairing_of_spacelike_from_local_normalCanonicalRayEOWBranchDataOn
bvt_W_swap_pairing_of_spacelike_from_pointwise_normalCanonicalRayEOWBranchDataOn
```

The first consumes exactly the support-local reduced-normal branch-data producer

```lean
∀ ξ ∈ tsupport φ, ∃ V, IsOpen V ∧ ξ ∈ V ∧
  ∀ ψ, HasCompactSupport ψ →
    tsupport ψ ⊆ V →
    ∀ η, ψ η ≠ 0 →
      Nonempty
        (AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn
          (AdjacentNormal.reducedCoord ... η))
```

The second reduces that support-local producer to the pointwise geometric
producer

```text
∀ p ∈ AdjacentNormal.reducedSelectedSpacelike,
  Nonempty (AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn ... p)
```

using `isOpen_reducedSpacelikeSwapEdge`, `subset_tsupport`, and the checked
normal-coordinate equivalence
`AdjacentNormal.reducedCoord_mem_reducedSelectedSpacelike_iff`.

Both then follow the checked chain

```text
ReducedNormalCanonicalRayEOWBranchDataOn
  -> ReducedLocalAdjacentBoundaryCLMInvariant
  -> ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
  -> bvt_W_swap_pairing_of_spacelike
```

These are not the missing analytic producer; they are the verified final-mile
consumers for the corrected producer.  The only theorem-2 locality gap left on
this route is the OS-I frozen-spectator mixed-tube/EOW construction of the
branch data above at arbitrary points of
`AdjacentNormal.reducedSelectedSpacelike`.

## 2026-06-02 Source-Side Domain Audit

The direct OS45 source-side membership proof was rechecked against the actual
domain definitions.  The relevant normal form is

```lean
BHW.os45FlatCommonChartSourceSide_mem_extendedTube_iff
```

which says that a signed source-side point is in the ordinary extended tube
exactly when its flattened common-chart representative lies in

```lean
BHW.os45FlatCommonChartOmega d n σ
```

and that domain is just the pullback

```lean
BHW.os45PulledRealBranchDomain (d := d) (n := n) σ
```

meaning: after undoing the OS45 quarter-turn and the branch label, the point is
in `BHW.ExtendedTube`.

The current cone-height source-side theorems

```lean
AdjacentNormal.eventually_sourceSide_coneHeight_upper_mem_extendedTube
AdjacentNormal.eventually_sourceSide_coneHeight_lower_mem_extendedTube
```

obtain that `Omega` membership only from the Figure-2-4 local wedge theorem

```lean
BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
```

whose real-edge inputs are the patch fields

```lean
P.V_pulled_id
P.V_pulled_tau
```

for a supplied

```lean
P : BHW.OS45Figure24CanonicalSourcePatchData ...
```

and a membership hypothesis

```lean
coordInv ... ((0 : SpacetimeDim d), p) ∈ P.V
```

Thus the `P.V` dependence is not cosmetic.  It is exactly the real-edge
extended-tube membership needed before openness gives the small two-sided wedge.
The hypothesis

```lean
p ∈ AdjacentNormal.reducedSelectedSpacelike ...
```

only asserts spacelikeness of the selected adjacent difference in reduced
normal coordinates.  The codebase has checked one-coordinate PET support in
`OSToWightmanReducedOneSpacelikePET.lean`, but no theorem promotes this to
real-edge membership in the many-point pulled branch domains above.  Such a
promotion would be stronger than the theorem-2 support hypothesis and would
amount to reintroducing the Jost-local route.

The minimal remaining OS-I producer is therefore:

```text
For each p in reducedSelectedSpacelike, build an open reduced-normal collar E,
open side domains Ωplus Ωminus containing SCV.realEmbed '' E, side branches
Fplus Fminus holomorphic on those domains, a common continuous boundary value
bv on E, and the two canonical-ray representation/asymptotic-transfer facts.
Then package them with
AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn.ofRealEdgeMem.
```

All topology after those real-edge and branch facts is already checked by
`ReducedNormalCanonicalRayEOWBranchDataOn.ofRealEdgeMem` and the final-mile
theorems in `OSToWightmanReducedBoundarySupport.lean`.

## 2026-06-02 No-Spectator PET Boundary Case

The `m = 1`, `i = 0`, `j = 1` no-spectator case is now separated from the
general frozen-spectator gap.  In that case the selected adjacent spacelike
coordinate is the whole reduced configuration, and Lean proves:

```lean
OSReconstruction.AdjacentNormal
  .reducedCoordInv_zero_one_mem_reducedPermutedExtendedTubeN_of_selected
OSReconstruction.AdjacentNormal
  .reducedCoordInv_noSpectator_mem_reducedPermutedExtendedTubeN_of_selected
```

The proof uses the inverse reduced normal chart identity
`AdjacentNormal.reducedCoordInv_right` and the adjacent projection identity
`reducedPairDiffCLM_adjacent_eq_proj`; no branch-domain or Figure-2-4 patch
data is involved.

The corresponding pointwise reduced boundary-value consequence is also checked:

```lean
OSReconstruction.AdjacentNormal
  .bvt_F_reduced_two_direction_pointwise_tendsto_zero_zero_one
OSReconstruction.AdjacentNormal
  .bvt_F_reduced_two_direction_pointwise_tendsto_zero_noSpectator
```

This confirms that, in the no-spectator case, the existing reduced PET
extension route is sufficient.  The remaining theorem-2 producer is specifically
the `m ≥ 2` frozen-spectator mixed-tube/EOW construction: selected
spacelikeness fixes only the head coordinate and still does not supply real-edge
membership for arbitrary spectators.

## 2026-06-02 Fixed-Flat OS45 Shortcut Audit

The direct conversion

```text
flat common-edge branch at x + i ε ηc
  ↦ canonical reduced branch at reducedDiff(x)
```

is not a valid coordinate identity.  Undoing the OS45 quarter-turn at fixed
flat height leaves a mixed time component with a `(1 + I) / 2` factor.  Thus
the reduced differences do not equal

```lean
ξ + ε • canonicalReducedDirectionC * Complex.I
```

The source-side chart instead uses

```lean
BHW.os45FlatCommonChartSourceSide ... ε ηc u
```

whose real part is shifted by `+ ε • ηc` at the same time as the imaginary
height is added.  The existing checked lemmas

```lean
AdjacentNormal.reducedDiffMap_coneHeight_sourceSide_eq_upperCanonicalRay
AdjacentNormal.reducedDiffMap_coneHeight_sourceSide_eq_lowerCanonicalRay
```

are therefore the correct coordinate bridge.  The next reduced-local-CLM
producer should combine the source-side moving/endpoint integral theorems with
the local zero source representation, not try to identify the fixed flat EOW
integral directly with the reduced canonical branch integral.

## 2026-06-03 Source-Oriented Producer Audit

The source-oriented scalar representative and real-compatible full-frame
kernel are useful route infrastructure, but they do not yet prove the missing
arbitrary-spectator theorem-2 producer.  The checked final consumer is still

```lean
bvt_W_swap_pairing_of_spacelike_from_pointwise_normalCanonicalRayEOWBranchDataOn
```

with pointwise input

```text
forall p in AdjacentNormal.reducedSelectedSpacelike,
  Nonempty (AdjacentNormal.ReducedNormalCanonicalRayEOWBranchDataOn ... p)
```

The `m = 1` no-spectator PET theorem

```lean
AdjacentNormal.reducedNormalCanonicalRayEOWBranchDataOn_noSpectator_of_selected
```

is only a sanity check for the case where the selected adjacent coordinate is
the whole reduced configuration.  It does not remove the frozen-spectator
mixed-tube/EOW obligation.

The source-oriented route should therefore target these three local leaves:

- `sourceOrientedSelectedReducedRealEdge_mem_extendedTubeDomain`: selected
  reduced-normal real-edge configurations map into the source-oriented
  extended-tube domain without strengthening the support point to a full Jost
  packet.
- `sourceOrientedSelectedReducedCanonicalRays_same_germ`: the upper and lower
  canonical reduced rays land in the same source-oriented invariant germ as
  the real-edge point for small positive height.
- `sourceOrientedSelectedReducedRayEOWBranchDataOn_of_normalRiemann`: assemble
  those two facts with `SourceOrientedNormalRiemannExtensionInput` and
  `sourceOrientedVarietyGermHolomorphicOn_extendF_descent_of_normalRiemann`
  into `ReducedNormalCanonicalRayEOWBranchDataOn`.

This keeps the producer local to the reduced selected-adjacent data rather than
re-entering the Figure-2-4 `P.V` route, whose real-edge membership is stronger
than the theorem-2 hypothesis for arbitrary frozen spectators.
