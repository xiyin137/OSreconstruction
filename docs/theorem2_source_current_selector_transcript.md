# Theorem 2 Source-Current Selector Transcript

Status: live transcript for the source-current selector audit in
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` and its faithful
Ruelle/Jost replacement surface.

This note is not a final theorem-2 closure declaration.  Its purpose is to
record which local selector steps are genuine and which must be replaced by
the book-route Ruelle/Jost input instead of hidden as endpoint rewrites.

## Latest Delta

May 24, 2026 local boundary handoff check:

```lean
BHW.proofideas_bvt_W_eq_of_selectedJostData_local_compactRealPatch
```

in

```text
test/proofideas_selected_jost_to_local_boundary_locality.lean
```

Verification:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  test/proofideas_selected_jost_to_local_boundary_locality.lean
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45SelectedCompact.lean
lake env lean -DmaxHeartbeats=1200000 \
  test/proofideas_boundary_locality_patch_cover_provider.lean
lake env lean -DmaxHeartbeats=1200000 \
  test/proofideas_os45_selected_jost_to_compact_packet.lean
```

All exit code `0`.  This is the checked downstream handoff from selected Jost
data to one local boundary-locality packet: `SelectedAdjacentDistributionalJostAnchorData`
plus adjacent ET-overlap connectedness gives
`BHW.os45CompactFigure24WickPairingEq_of_selectedJostData`, and the existing
canonical-shell consumer gives compact-test equality for tests whose
topological support lies in that packet's identity real patch.

This does **not** close the public Theorem-2 locality sorry.  The remaining
non-wrapper producer is now the classical OS I section 4.5/Jost compact-cover
theorem:

```lean
∀ f : SchwartzNPoint d n,
  HasCompactSupport (f : NPointDomain d n → ℂ) →
  (∀ x, f.toFun x ≠ 0 →
    MinkowskiSpace.AreSpacelikeSeparated d
      (x i) (x ⟨i.val + 1, hi⟩)) →
  ∃ (α : Type) (_ : Fintype α),
    ∃ hCompact : α → BHW.OS45CompactFigure24WickPairingEq
        (d := d) n i hi OS lgc,
      tsupport (f : NPointDomain d n → ℂ) ⊆
        ⋃ a : α, (hCompact a).realPatch 1
```

That is the next theorem to prove faithfully from the book route: local Jost
patches around each adjacent-spacelike real configuration, compact finite
subcover, then the already checked boundary transfer.  A bare Hdiff germ at
the canonical source patch is insufficient unless its real patch is transported
to cover the actual support point.

Promoted the local `S'_n` branch-to-pair-data bridge on May 22, 2026:

```lean
BHW.os45_BHWJostPairData_of_zeroHeight_pairingsCLM
BHW.os45CompactFigure24WickPairingEq_of_sPrimeBranchData
BHW.os45_BHWJostPairData_on_figure24SourcePatch_of_zeroHeight_pairingsCLM
BHW.os45CompactFigure24WickPairingEq_of_zeroHeight_pairingsCLM
```

in

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45PairData.lean
```

Scratch gate:

```bash
lake env lean test/proofideas_os45_pairdata_from_sprime_seed.lean
```

Production verification:

```bash
lake env lean \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45PairData.lean
```

Both exit code `0`; targeted scan of the new files has no
`sorry`/`admit`/`axiom`, and `git diff --check` passes.  The mathematical
content is the checked Stage C -> D -> E carrier assembly: zero-height
common-edge EOW pairings produce the local S-prime seed, the authorized local
BHW theorem produces one branch on the selected two-sector hull, `S.toPairData`
turns that branch into the source-patch BHW/Jost pair carrier, and the existing
compact constructor turns the pair carrier into an
`OS45CompactFigure24WickPairingEq`.  The remaining producer is now sharper:
construct the zero-height common-edge pairing family, or equivalently the
local `S'_n` branch data, for the compact adjacent-spacelike patch cover.

Promoted the adjacent boundary-locality density bridge on May 22, 2026:

```lean
BHW.bvt_W_eq_of_compactFigure24Patch_at_tsupport
BHW.bvt_W_adjacent_swap_of_compactFigure24Patch_cover_provider
```

in

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityCanonicalShell.lean
```

Scratch gate:

```bash
lake env lean test/proofideas_boundary_locality_patch_cover_provider.lean
```

Production verification:

```bash
lake env lean \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityCanonicalShell.lean
```

Both exit code `0`; `git diff --check` passes on the touched files.  The
mathematical content is the final density step for the public adjacent
`bvt_W` locality statement plus the finite-subcover extraction just before it.
First, a local packet at every point of a compact topological support gives a
finite packet family by compactness.  Second, arbitrary Schwartz tests are
reduced to compactly supported adjacent-spacelike truncations, and each compact
truncation is handled by the checked finite Figure-2-4 patch-cover theorem.
The remaining producer is now precisely the local packet/compact-cover
statement for adjacent-spacelike supports.

Corrected the Hdiff producer surface on May 22, 2026.  The direct finite
chart-corridor proof had reached the genuine circular leaf

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

Endpoint DCT and chart-overlap retargeting do not prove this leaf.  The
faithful Jost/Ruelle route supplies the missing content as selected
distributional Jost anchor data plus adjacent overlap connectedness.  The
production theorem

```lean
BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45
```

now exposes those inputs explicitly:

```lean
(hOverlap :
  ∀ (j : Fin n) (hj : j.val + 1 < n),
    IsConnected
      {z : Fin n → Fin (d + 1) → ℂ |
        z ∈ BHW.ExtendedTube d n ∧
          BHW.permAct (d := d)
            (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
            BHW.ExtendedTube d n})
(hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n)
```

and delegates to the checked Ruelle producer
`BHW.os45_hdiff_of_selectedJostData`.

Scratch gate:

```bash
lake env lean test/proofideas_hdiff_selected_adapter.lean
```

Production verification:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Both exit code `0`.  A targeted scan of the touched Lean files finds no
`sorry`/`admit`/`axiom`.

Promoted the OS45 source-side affine-ray coordinate lemma on May 22, 2026:

`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45SourceSide.lean`
now contains

```lean
BHW.os45FlatCommonChartSourceSideDirection
BHW.os45FlatCommonChartSourceSide_affine
```

The theorem proves the exact coordinate identity

```lean
os45FlatCommonChartSourceSide d n rho sgn eps eta u
  =
os45FlatCommonChartSourceSide d n rho sgn 0 eta u
  + fun k mu => (eps : Complex) *
      os45FlatCommonChartSourceSideDirection rho sgn eta k mu
```

This is only the straight-ray algebra for the positive source-side current.
It does not select a boundary value and does not compare the source-side
endpoint with the Wick endpoint.  It is the neutral coordinate input needed
before stating the honest scalar OS/Jost boundary theorem for the live
`SourcePathMoving - WickPathMoving` gap.

Verification:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45SourceSide.lean
```

Exit code `0`; no `sorry`/`admit`/`axiom` matches in the touched Lean file.

Started a pinned Gemini Deep Research theorem-shape check for the live Hdiff
selector:

```text
v1_Chd3VnNRYXNDcExMTDl4TjhQcHVqUXNBYxIXd1ZzUWFzQ3BMTEw5eE44UHB1alFzQWM
```

The question asks whether the finite chart-corridor proof should try to prove
the source-path/Wick-path limit directly, or whether the faithful OS/Jost
route is to redirect the current theorem surface through the already checked
scalar real-edge/Ruelle-overlap producer.  The interaction is currently
`in_progress`.

Fresh Hdiff verification after the support edit:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/tmp/osr_hdiff_after_affine_1779457050.log`, exit code `1`.

The ordinary hard goal is unchanged:

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

The context already contains the endpoint and retargeting facts
`hSourcePathMoving_endpoint`, `hWickPathMoving_selected`,
`hpath_Aext_transport_equiv`, and `hSourceMovingExtendF_gap_limit`.  This
confirms the current diagnosis: endpoint DCT reaches the source-side endpoint,
and Wick DCT selects the Schwinger value, but the proof still needs the
OS/Jost distributional current transport between those two boundary values.

Checked the theorem-2 adjacent-overlap narrowing on May 22, 2026:

`test/proofideas_adjacent_overlap_direct_connected.lean` records the local
Figure-2-4 replacement for the generic permutation-flow blocker.  It proves
that a single adjacent real double-coset generation packet for
`BHW.adjSwapForwardOverlapIndexSet` gives connectedness of the adjacent
extended-tube overlap:

```lean
BHW.proofideas_adjacent_overlap_connected_of_real_double_coset_generation
```

The production bridge now lives in
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean`:

```lean
bvt_selectedAdjacentOverlap_connected_of_adjacentIndexGeneration
bvt_selectedAdjacentOverlap_connected_of_adjacentIndexGeneration_all
bvt_F_selectedAdjacentPermutationEdgeData_of_selectedJostData_and_adjacentIndexGeneration
```

This does not prove the double-coset generation itself.  It removes ambiguity
about the next theorem-2 geometry target: prove the adjacent-index generation
for the local swap, then feed the already-checked selected-witness/Ruelle
consumer.  The broader
`BHW.blocker_isConnected_permSeedSet_nontrivial` remains generic
permutation-flow infrastructure, not the preferred theorem-2 connectedness
surface.

Verification:

```bash
lake env lean test/proofideas_adjacent_overlap_direct_connected.lean
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean
```

All exit code `0`.  A scan of the touched Lean files finds no
`sorry`/`admit`/`axiom`.

Checked finite Figure-2-4 patch-cover assembly on May 22, 2026:

`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityCanonicalShell.lean`
now exposes

```lean
BHW.bvt_W_eq_swapped_of_finite_compactFigure24Patch_cover
BHW.bvt_W_eq_of_finite_compactFigure24Patch_cover
```

This theorem partitions a compactly supported test subordinate to finitely many
identity real patches carrying `OS45CompactFigure24WickPairingEq`, applies the
local canonical-shell/Wightman equality on each piece, and re-sums by
`bvt_W_linear`.  The second statement exposes the same result for an arbitrary
swapped test `g` satisfying the usual pointwise swap equation.  This closes the
finite partition assembly step but does not assert that arbitrary
adjacent-spacelike compact support admits such a cover.  That remaining
producer is still the Jost/Ruelle/OS-I compact boundary theorem.

Verification:

```bash
lake env lean test/proofideas_locality_finite_patch_cover.lean
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityCanonicalShell.lean
```

Both exit code `0`.

Checked and promoted the local `S'_n` consumer on May 22, 2026:

`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean`
now exposes

```lean
BHW.os45_hdiff_of_sPrimeBranchData_local
```

The theorem proves the OS45 Hdiff germ directly from
`OS45BHWJostSPrimeBranchData`, with no global adjacent-overlap connectedness
input.  Its proof takes `Ucx := H.ΩJ` and `Hdiff := 0`; the common-edge trace is
the equality of the ordinary and adjacent restrictions of the same local
`S'_n` branch.  This narrows the remaining genuine producer to the local EOW
seed / selected-data Ruelle seed that constructs the `S'_n` branch.

Verification:

```bash
lake env lean test/proofideas_os45_hdiff_from_sprime_branch_local.lean
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean
```

Both exit code `0`.

Checked a negative Lean probe for the remaining adjacent-overlap geometry on
May 22, 2026:

`test/proofideas_forward_tube_swap_warning.lean` proves

```lean
BHW.proofideas_forwardTube_swap_counterexample_mem
BHW.proofideas_forwardTube_swap_counterexample_not_mem
```

The concrete `d = 1`, `n = 2` example lies in the public successive-difference
`ForwardTube`, but its adjacent swap does not.  Thus the tempting shortcut
`adjSwapForwardOverlapSet = ForwardTube` is false.  The adjacent-overlap
connectedness needed for the E->R route has to be the genuine Jost/Ruelle
connectedness of `T'_n ∩ s_i T'_n`, not a permutation-invariance fact about
the base forward tube.

Verification:

```bash
lake env lean test/proofideas_forward_tube_swap_warning.lean
```

Exit code `0`.

The previous pinned Deep Research overlap interaction
`v1_ChdpOTRQYXRDZUZKamtuc0VQZ28yVnNRaxIXaTk0UGF0Q2VGSmprbnNFUGdvMlZzUWs`
failed with an API-side processing error.  A replacement pinned Deep Research
interaction is running as
`v1_ChdDLVVQYXJ6QkJwX1B2ZElQcHRfaDZBSRIXQy1VUGFyekJCcF9QdmRJUHB0X2g2QUk`.

Promoted selected-data flat seed from scratch to production on May 22, 2026:

`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean`
now exposes

```lean
BHW.os45_flat_seed_of_selectedJostData
```

This is the production version of the checked replacement for the long
per-piece fixed-selector endpoint route.  From
`SelectedAdjacentDistributionalJostAnchorData`, adjacent ET-overlap
connectedness, and the local Ruelle common-edge source window, it produces the
connected open initial-sector `EqOn` seed needed by the Figure-2-4 flat
common-chart route.  It does not construct the selected data or the adjacent
overlap connectedness; those remain the honest Jost/Ruelle/OS-I producers.

Verification:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean
```

Exit code `0`.

Checked Step-5 boundary geometry and d=0 connectedness warning on May 22,
2026:

`OSReconstruction/ComplexLieGroups/JostRuelleStep5.lean` now contains the
first production Step-5 boundary facts needed by the faithful Jost/Ruelle
packet:

```lean
BHW.jostRuelleStep5Seed_mem_forwardTube
BHW.jostRuelleStep5RealBoundaryReal
BHW.jostRuelleStep5RealBoundary_eq_ofReal
BHW.jostRuelleStep5RealBoundary_spacelike
BHW.jostRuelleStep5RealBoundary_mem_extendedTube
```

These prove that the explicit seed `(i, -cot φ, 0, ...)` is in the one-point
forward tube, that the real boundary vector is spacelike when `sin φ ≠ 0`, and
that the corresponding complex boundary point lies in the extended tube as the
`L(iφ)` image of the seed.  This is direct Jost Appendix-II Step-5 geometry,
not an endpoint selector replacement.

The scratch file `test/proofideas_permseed_d0_counter_surface.lean` also proves

```lean
BHW.proofideas_permSeedSet_d0_nontrivial_empty
BHW.proofideas_not_isConnected_permSeedSet_d0_nontrivial
```

showing that the current dimension-polymorphic
`blocker_isConnected_permSeedSet_nontrivial` statement is too strong at
`d = 0`: nontrivial permutation seed overlap is empty there, while mathlib
`IsConnected` includes nonemptiness.  The theorem-2 route has `hd : 2 ≤ d`, so
the next connected-overlap surface should be dimension-split or carry the
nonzero/high-dimensional hypothesis explicitly.

The production blocker surface has therefore been corrected:
`BHW.blocker_isConnected_permSeedSet_nontrivial` now requires `[NeZero d]`, and
`BHW.bvt_selectedAdjacentOverlap_connected_of_permSeedGeometry` carries that
same nonzero-dimensional call-site surface.  This does not close the two
existing blocker `sorry`s; it removes the false dimension-zero obligation from
the E->R-critical geometry route.

Verification:

```bash
lake env lean OSReconstruction/ComplexLieGroups/JostRuelleStep5.lean
lake env lean test/proofideas_permseed_d0_counter_surface.lean
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean
lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean
lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean
```

All exit `0` (the blocker file still reports the two existing `sorry`
warnings; `PermutationFlow.lean` has older warnings/try-this output).

Fresh Deep Research interaction
`v1_ChdVOFVQYW9HdEZJT1p2ZElQNFlQTDhRaxIXVThVUGFvR3RGSU9admRJUDRZUEw4UWs`
completed.  Its route verdict agrees with the current correction: a direct
`SourcePathMoving`/`WickPathMoving` contour homotopy over boundary values is
not the faithful proof surface; construct
`SelectedAdjacentDistributionalJostAnchorData` and adjacent ET-overlap
connectedness from Vladimirov/Jost/Bogoliubov Edge-of-the-Wedge boundary data,
then feed the checked Ruelle common-edge compact-test boundary consumer.
Raw response saved at `/tmp/gemini_os45_next_surface_completed.json`.

Checked selected-data-to-flat-seed scratch splice on May 22, 2026:

`test/proofideas_os45_selected_data_to_flat_seed.lean` now proves

```lean
BHW.proofideas_os45_flat_seed_of_selectedJostData
```

with no `sorry`/`admit`/`axiom`.  The theorem composes the production
selected-data compact-test boundary theorem

```lean
BHW.os45_ruelle_commonEdge_boundary_hint_of_selectedJostData
```

with the production Ruelle consumer

```lean
BHW.os45_initialSectorEqOn_open_of_ruelle_commonEdge_boundary
```

and produces exactly the local initial-sector EqOn seed shape currently needed
at Hdiff's `hflat_seed` block:

```lean
∃ W,
  IsOpen W ∧ IsPreconnected W ∧
  commonEdgeSeed u0 ∈ W ∧
  W ⊆ ExtendedTube d n ∩ permutedExtendedTubeSector d n P.τ ∧
  Set.EqOn (extendF (bvt_F OS lgc n))
    (fun z => extendF (bvt_F OS lgc n) (permAct P.τ z)) W
```

Verification:

```bash
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap
lake env lean test/proofideas_os45_selected_data_to_flat_seed.lean
```

Both exit `0`.  This confirms the production replacement shape for the old
per-piece fixed selector: construct the selected Jost/Ruelle compact-test
boundary packet and adjacent overlap connectedness, then feed this seed into
Hdiff.  It is not a proof of the selected data itself and should not be read
as a closure of the OS-I/Jost producer.

Checked flat-pairings-to-Ruelle-hint scratch theorem on May 22, 2026:

`test/proofideas_os45_ruelle_hint_from_flat_pairings.lean` now proves

```lean
BHW.proofideas_ruelle_commonEdge_hint_of_flat_zeroHeight_pairings
```

with no `sorry`/`admit`/`axiom`.  The theorem states that if the old flat
zero-height ordinary and adjacent pairings have already been selected against
the same CLM `T`, then the new Ruelle common-edge compact-test boundary
hypothesis follows after the checked common-edge change of variables and
cutoff removal.  It uses

```lean
BHW.os45FlatCommonChart_ordinaryCommonBoundary_integral_eq_sourcePullback
BHW.os45FlatCommonChart_adjacentCommonBoundary_integral_eq_sourcePullback
D.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
```

and cancels the nonzero Jacobian `BHW.os45CommonEdgeFlatJacobianAbs n`.

Verification:

```bash
lake env lean test/proofideas_os45_ruelle_hint_from_flat_pairings.lean
```

Exit code `0`.

This pins the current route correction.  The Ruelle theorem surface is the
right consumer, but feeding it from the already-selected flat plus/minus
zero-height pairings is not a new proof of the OS-I content; it is equivalent
bookkeeping.  The next genuine producer remains the transformed-test
Jost/Ruelle current equality that constructs the common-edge compact-test
boundary packet directly from OS I §4.5/Jost spacelike data, without first
forcing the individual fixed selector.

The Deep Research interaction
`v1_ChZ6YVVQYXZibk90YWMyOG9QaXJUUFVREhZ6YVVQYXZibk90YWMyOG9QaXJUUFVR`
completed and agrees with this correction: the primary theorem surface should
be transformed-test contour homotopy/current equality, not pointwise endpoint
selection.  Raw response saved at
`/tmp/gemini_os45_current_transport_completed.json`.

Production Ruelle-to-flat connector checked on May 22, 2026:

The scratch OS45 Ruelle splice has now been promoted to
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean`.
The checked production theorem surface is:

```lean
BHW.os45_sourceCommonEdge_eqOn_of_ruelleOverlap_extendF_pair_eqOn
BHW.os45_initialSectorEqOn_open_of_ruelleOverlap_extendF_pair_eqOn
BHW.os45_initialSectorEqOn_open_of_ruelle_linearReal_boundary
BHW.os45_initialSectorEqOn_open_of_ruelle_commonEdge_boundary
```

Verification:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean
lake env lean test/proofideas_os45_hdiff_current_transport_blueprint.lean
```

Both commands exit `0` (the scratch file still has older unused-`simp`
warnings).  The remaining theorem-2 packet is unchanged mathematically but is
now production-shaped: prove the concrete common-edge compact-test boundary
equality

```lean
∫ x, extendF(bvt_F)
        (Q.symm (realEmbed (os45CommonEdgeRealPoint 1 x))) * ρ x
  =
∫ x, extendF(bvt_F)
        (permAct P.τ
          (Q.symm (realEmbed (os45CommonEdgeRealPoint 1 x)))) * ρ x
```

for compactly supported tests `ρ` supported in the selected Figure-2-4 real
source window.  This is the Jost/Ruelle real-boundary packet to construct from
OS I §4.5/Appendix II Step 5.  The checked edge-chain and partition machinery
inside Hdiff still exposes the same fact from the old selector direction: the
ordinary leaf reduces to a localized moving source-side current versus Wick
current comparison, and endpoint DCT alone gives only the wrong endpoint.

Checked Ruelle-to-flat-EOW splice on May 22, 2026:

The scratch file
`test/proofideas_os45_hdiff_current_transport_blueprint.lean` now proves

```lean
BHW.proofideas_sourceCommonEdge_eqOn_of_overlap_extendF_pair_eqOn
BHW.proofideas_initialSectorEqOn_open_of_overlap_extendF_pair_eqOn
BHW.proofideas_initialSectorEqOn_open_of_ruelle_linearReal_boundary
BHW.proofideas_initialSectorEqOn_open_of_ruelle_os45_commonEdge_boundary
```

This is the Lean-facing connector for the corrected route.  If the Ruelle/Jost
overlap step supplies equality of the two deterministic branches

```lean
extendF (bvt_F OS lgc n)
fun z => extendF (bvt_F OS lgc n) (permAct P.τ z)
```

on a complex neighborhood containing the horizontal Figure-2-4 common-edge
section, then the existing source-common-edge consumer

```lean
BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_sourceCommonEdge_eqOn
```

gets exactly the pointwise `hsource_eq` it requires.  Thus the remaining
mathematical packet is now sharply isolated: construct the OS45
Ruelle/Jost boundary-distribution input that proves this deterministic overlap
equality.  The old per-piece fixed source-current selector is a consequence of
such a seed, not the right primary target.  The second scratch theorem packages
the full replacement shape for the current `hflat_seed` block: Ruelle overlap
equality on the common-edge neighborhood directly yields the local initial
sector EqOn seed currently produced through the long fixed-selector proof.  The
new OS45 specialization fixes the abstract linear section to

```lean
L = (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
R = BHW.os45CommonEdgeRealCLE (d := d) (n := n) 1
```

so the remaining `hint` is exactly the compact-test distributional equality on
the Figure-2-4 real source window:

```lean
∫ x, extendF(bvt_F) (Q.symm (realEmbed (commonEdge x))) * ρ x
  =
∫ x, extendF(bvt_F) (permAct P.τ (Q.symm (realEmbed (commonEdge x)))) * ρ x
```

This is now the next honest OS45/Jost/Ruelle producer.  It is not an endpoint
selector and not a pointwise real-edge shortcut.

Additional Ruelle overlap reducers on May 22, 2026:

`OSToWightmanRuelleOverlap` now contains checked identity-theorem reducers for
connected open subsets of `T'_n ∩ τT'_n`:

```lean
BHW.ruelleOverlap_eqOn_of_distributional_wickSection_eq_on_realOpen
BHW.ruelleOverlap_eqOn_of_distributional_realSection_eq_on_realOpen
BHW.ruelleOverlap_eqOn_of_distributional_linearRealSection_eq_on_realOpen
BHW.ruelleOverlap_extendF_pair_eqOn_of_distributional_wickSection_eq_on_realOpen
BHW.ruelleOverlap_extendF_pair_eqOn_of_distributional_realSection_eq_on_realOpen
```

The real-section theorem is the faithful Jost/Ruelle boundary shape: compact
test distributional equality on a real-open patch inside the overlap is first
converted to pointwise equality by distributional uniqueness, then propagated
by the totally-real identity theorem.  The linear-section theorem adds the
coordinate-change form needed for OS45: a complex linear equivalence on the
analytic variables and a real linear equivalence on the boundary variables.
This still does not close Hdiff by itself: the missing OS45 producer is now
the concrete boundary-distribution packet placing the Figure-2-4 real
spacelike/current data into this reducer, not an endpoint-value equality for
the fixed current.

Fresh Ruelle production substrate on May 22, 2026:

The Jost/Ruelle pivot now has two checked production companions:

```lean
OSReconstruction.ComplexLieGroups.JostRuelleStep5
OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap
```

`JostRuelleStep5` proves the generic-`d` Appendix-II Step-5 block
`L(iφ)` as an actual `ComplexLorentzGroup d`, including determinant one,
metric preservation, and

```lean
BHW.jostRuelleLiPhiCLG_action_seed_eq_realBoundary
```

which sends `(i, -cot φ, 0, …)` to `(0, -(sin φ)⁻¹, 0, …)`.

`OSToWightmanRuelleOverlap` exposes the honest overlap theorem surface:

```lean
BHW.ruelleOverlapDomain d n τ
BHW.ruelleUnionDomain d n τ
BHW.RuelleOverlapAnalyticInputs
BHW.RuelleDistributionalBoundaryAgreementOn
BHW.RuelleOverlapConclusion
BHW.ruelleOverlapAnalyticInputs_extendF_pair
```

The ordinary/permuted `extendF` branch pair is now verified to satisfy the
holomorphy and complex-Lorentz-invariance inputs on
`T'_n ∩ τT'_n`.  The remaining missing production theorem is the OS-free
Ruelle Appendix-II uniqueness step from distributional boundary agreement on
the real spacelike patch to branch equality on that overlap.  This is the
theorem that should replace the current per-piece
`SourcePathMoving - WickPathMoving` selector leaf in Hdiff.

Checks:

```bash
lake env lean OSReconstruction/ComplexLieGroups/JostRuelleStep5.lean
lake build OSReconstruction.ComplexLieGroups.JostRuelleStep5
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap
lake env lean test/proofideas_os45_hdiff_current_transport_blueprint.lean
```

All five checks succeed.  A fresh Hdiff check logged at
`/tmp/osr_hdiff_current_1779403474.log` still fails at the genuine
source/Wick transport goal and later timeout fallout; no endpoint-value
shortcut was reintroduced.

Fresh literal-adjacent guardrail on May 21, 2026:

The scratch file now proves the direct `permAct` form of the adjacent Wick
obstruction:

```lean
BHW.proofideas_os45Figure24_permAct_ordinaryWick_not_mem_forwardTube
```

For `u ∈ P.V`, the point

```lean
BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k))
```

is the raw adjacent Wick trace and is not in `BHW.ForwardTube d n`.  Therefore
the tempting literal difference branch
`extendF (bvt_F OS lgc n) (permAct P.τ z) - extendF (bvt_F OS lgc n) z`
still cannot provide the adjacent Wick trace by
`extendF_eq_on_forwardTube`.  Any production closure must use the raw OS412
preimage-forward-tube seed, or a real current-transport theorem carrying the
integration chain and test through the local BHW corridor.

Fresh source-text correction on May 21, 2026:

I checked the local text extraction of OS I, Section 4.  Equation `(4.14)` is
not itself a compact source-current transport theorem.  In the paper it is the
Lorentz-covariance infinitesimal identity

```text
X_ij W_n(q_1, ..., q_n) = 0
```

for the Fourier-Laplace reconstructed distributions, derived from `(4.12)`,
`(4.15)`, `(4.16)`, `(4.17)`, Lemma 8.4, and uniqueness of Laplace/Fourier
transforms.  Section 4.5 then says locality follows because the Wightman
functions have a single-valued symmetric analytic continuation into the BHW
domain, using Euclidean symmetry plus `(4.1)`, `(4.12)`, and `(4.14)`.

Consequently the live Lean leaf should not be described as a direct
application of formula `(4.14)` to the Figure-2-4 source-side current.  The
missing theorem is the derived compact-test/local-BHW consequence that turns
that OS-I analytic-continuation package into the specific source/Wick current
comparison on the current support.  Treating `(4.14)` as a standalone
source-current selector would hide the same gap behind a paper citation.

Fresh Deep Research v2 correction on May 21, 2026:

The pinned API-backed Deep Research consult
`deep-research-max-preview-04-2026` completed at
`/private/tmp/gemini_os45_current_transport_v2_result.json`.  Its useful route
correction is to abandon individual endpoint selectors and prove a
difference-current theorem by transporting the compact test/current through
the holomorphic bulk.  However, its slogan "prove equality for every positive
height" must not be read as a same-weight equality following from holomorphy
alone.  The checked scratch theorem

```lean
BHW.proofideas_same_branch_holomorphy_does_not_give_bulk_equality
```

shows that one holomorphic branch is not enough: even the identity function
changes under a nonzero translation.  The production theorem must therefore
carry the transformed integration chain, test, and boundary-term cancellation
explicitly.  If the natural source and Wick slots use different weights, the
Lean theorem surface must expose that comparison instead of asserting an
unsupported eventual equality.

Fresh exact Hdiff check:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/private/tmp/osr_hdiff_current_2076.log`.  It terminates with exit code
`1`.  The first non-timeout hard proof error is still line `5976`:

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

The later timeout diagnostics remain downstream elaboration fallout after Lean
continues through this unfinished current transport.

Fresh scratch narrowing on May 21, 2026:

The scratch file now also proves

```lean
BHW.proofideas_os45Figure24_not_all_lorentzInvariantScalars_identify_endpoints
```

This is the Lean-facing form of the latest route correction.  It says that the
ordinary Figure-2-4 endpoints are not identified by pointwise
complex-Lorentz-invariance as a general principle: a checked
complex-Lorentz-invariant source-Gram scalar separates them.  Therefore the
live Hdiff comparison cannot be closed by a generic endpoint-value invariance
rewrite.  The remaining producer is still the distributional/current
transport equating the compact positive source-side current with the Wick
current, after the already checked finite chart retargeting.

Fresh scratch check:

```bash
lake env lean test/proofideas_os45_hdiff_current_transport_blueprint.lean
```

terminates with exit code `0`.  A scratch/Hdiff scan for
`sorry`/`admit`/`axiom` has no matches.

Fresh process/Lean-scratch update on May 21, 2026:

The scratch file now additionally proves

```lean
BHW.proofideas_os45Figure24_sourceSide_zero_not_any_wickRotate
BHW.proofideas_os45Figure24_lorentzInvariantScalar_separates_endpoints
```

This strengthens the endpoint audit: the ordinary source-side zero endpoint is
not a Wick rotation of any real Euclidean configuration on the source patch,
because its time coordinate has positive real part whereas a Wick-rotated time
coordinate is purely imaginary.  The diagonal source Gram coordinate is also a
checked complex-Lorentz-invariant scalar that separates the raw Wick endpoint
from the source-side endpoint on the positive source patch.  Thus the missing
selector cannot be closed by changing the real Euclidean source variable under
the Wick map or by pointwise complex-Lorentz invariance; it must still be an
OS-I current transport through the Figure-2-4 corridor.

Fresh exact Hdiff check:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/private/tmp/osr_hdiff_current_1779321034.log`.  It terminates with exit
code `1`.  The first hard proof error is still line `5976`, the ordinary
source/Wick moving-current transport:

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

The later diagnostics in that log are deterministic timeouts after Lean
continues past the unfinished transport proof.

Additional scratch narrowing on May 21, 2026, later in the same pass:

The checked scratch file
`test/proofideas_os45_hdiff_current_transport_blueprint.lean` now also proves

```lean
BHW.proofideas_os45Figure24_identityPath_endpoint_sourceGram_ne
BHW.proofideas_os45Figure24_identityPath_endpoint_not_complexLorentzOrbit
```

The first theorem proves that the ordinary Figure-2-4 identity-path endpoints
`t = 0` and `t = 1` have different complex Minkowski source Gram matrices on
the positive source patch.  The second packages the consequence: the Wick
endpoint and the source-side zero endpoint are not connected by a single
complex Lorentz transformation.  This refutes the Gemini orbit-invariance
shortcut in the formal geometry.  The missing current transport is therefore a
real OS-I boundary-current theorem, not pointwise constancy of `extendF` along
one complex-Lorentz orbit.

Fresh scratch check:

```bash
lake env lean test/proofideas_os45_hdiff_current_transport_blueprint.lean
```

terminates with exit code `0`.

Additional scratch narrowing on May 21, 2026:

The checked scratch file
`test/proofideas_os45_hdiff_current_transport_blueprint.lean` now also proves

```lean
BHW.proofideas_os45Figure24_sourceSide_zero_eq_identityPath_one
BHW.proofideas_os45Figure24_sourceSide_zero_not_realEmbed
```

The first theorem identifies the ordinary source-side zero endpoint with the
`t = 1` endpoint of `BHW.os45Figure24IdentityPath`; the raw Wick point is the
`t = 0` endpoint.  The second theorem proves that the same source-side endpoint
is not a real embedded Euclidean configuration on the source patch.  Thus the
ordinary real-ray boundary theorem

```lean
bvt_boundary_values_moving
```

cannot be used by re-centering at a hidden real base point.  The live current
transport must cross the Figure-2-4 identity-path/BHW-Jost corridor, or use an
equivalent OS-I `(4.14)` compact-test theorem that already contains that
transport.

Fresh scratch check:

```bash
lake env lean test/proofideas_os45_hdiff_current_transport_blueprint.lean
```

terminates with exit code `0`, and the scratch/Hdiff token scan for
`sorry`/`admit`/`axiom` has no matches.  A pinned API-backed Gemini Deep
Research consult using `deep-research-max-preview-04-2026` is running at
`/private/tmp/gemini_os45_current_transport_result.json` to sanity-check the
exact theorem surface and whether OS I supplies this as a compact-test
current-transport theorem or only a weaker distributional edge statement.

The route decision from the #2071 audit is now externalized before any
production edit.  I added the harness rule to `agent.md` and `CLAUDE.md`:
hard proof routes must be written in a maintained blueprint/proof-audit doc or
encoded in a Lean scratch file under `test/` / `Proofideas/` before production
Lean is touched.

I also added the checked scratch file
`test/proofideas_os45_hdiff_current_transport_blueprint.lean`.  Its concrete
Lean lemma

```lean
BHW.proofideas_os45Figure24_adjacentWick_not_mem_forwardTube
```

proves that for `u ∈ P.V`,

```lean
(fun k => wickRotatePoint (u (P.τ k))) ∉ BHW.ForwardTube d n
```

using the existing ordinary Wick forward-tube membership and
`BHW.permutedForwardTube_forces_perm_one`.  This makes the #2071 caveat
Lean-facing: the adjacent trace field for
`BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3` cannot be filled by applying
`extendF_eq_on_forwardTube` to the adjacent Wick point.  The direct E3 refactor
therefore still needs a genuine raw adjacent/source-current transport theorem.

The exact scratch check

```bash
lake env lean test/proofideas_os45_hdiff_current_transport_blueprint.lean
```

terminated with exit code `0`.

I then extended the same checked scratch file with two ordinary-side sanity
lemmas:

```lean
BHW.proofideas_os45Figure24_sourceSide_zero_mem_forwardTube
BHW.proofideas_os45Figure24_sourceSide_zero_ne_rawWick
```

The first proves that the live ordinary source-side zero endpoint

```lean
BHW.os45FlatCommonChartSourceSide d n 1 1 0 η u
```

is an ordinary forward-tube point for `u ∈ P.V`.  The second proves that this
endpoint is not the raw Wick point

```lean
fun k => wickRotatePoint (u k)
```

on the Figure-2-4 source patch.  Thus the blocker is now Lean-facing in both
directions: it is not a domain-membership problem, and it is not a definitional
endpoint simplification.  The missing step must identify the distributional
current carried by this quarter-turned endpoint/source-side family with the
Wick/Schwinger current.

The scratch file still checks with:

```bash
lake env lean test/proofideas_os45_hdiff_current_transport_blueprint.lean
```

exit code `0`.

The current exact Hdiff check was captured at
`/private/tmp/osr_hdiff_current_1779317864.log`:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

It terminates with exit code `1`.  The first hard error remains line `5976`,
the ordinary moving source/Wick comparison:

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

Later diagnostics include deterministic timeouts after Lean continues past
that unfinished proof body; the first mathematical blocker is still the
ordinary current transport above.

Fresh route check on May 20, 2026 22:22 CEST:

The pinned Gemini Deep Research reroute consult completed with
`deep-research-max-preview-04-2026` and independently rejected the direct
`Hdiff := extendF(bvt_F)(permAct P.τ z) - extendF(bvt_F) z` bypass.  Its
diagnosis matches the Lean state: the interior/common-edge bookkeeping is not
the obstruction; the boundary trace reduces back to

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

I rechecked the theorem surfaces after the consult.  The moving source-side
DCT theorem

```lean
BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
```

only proves convergence to the already selected zero-height source endpoint.
The source-pairing theorem

```lean
OS45Figure24SourceCutoffData.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
```

controls Wick pairings, including the E3 adjacent Wick rewrite, but it does
not control the `extendF(sourceSide eps u)` pairing.  A targeted scan found
general Cauchy/contour infrastructure and real-edge moving BV infrastructure,
but no checked OS45 theorem equating the live source-side current with the
Wick current.

So the honest remaining theorem shape is still the compact OS-I `(4.14)`
source-current transport for the specific `os45FlatCommonChartSourceSide`
family and the same moving side-zero weight.  The proof should not add another
endpoint or chart wrapper around the equivalent local identity

```lean
Tlocal pieceFlat = BHW.os45CommonEdgeFlatJacobianAbs n * OS.S n pieceZD
```

because that identity is precisely the missing current transport.

Fresh route check on May 20, 2026 16:12 CEST:

Latest exact-check log: `/tmp/osr_hdiff_current_1779286221.log`.

The ordinary refined leaf is still

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

I rechecked the nearby source-side moving support theorem:

```lean
BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
```

It is useful, but only after a branch value has already been selected.  It
proves the moving-test source-side integral tends to its zero-height endpoint
on the same local branch.  It does not compare that zero-height source-side
endpoint with the Wick current.

The endpoint mismatch is now explicit.  The live source-side endpoint is

```lean
BHW.os45FlatCommonChartSourceSide d n 1 1 0 η u
  = (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed (BHW.os45CommonEdgeRealPoint d n 1 u))
```

whereas the Wick Schwinger anchor comes from

```lean
fun k => wickRotatePoint (u k)
```

The Figure-2-4 path lemmas put these two configurations in the checked forward
tube/initial-sector corridor, and the chart-chain facts identify branch names
on carrier intersections.  They still do not prove a current equality along
the corridor.  The support theorem
`os45FlatCommonChart_wickSection_sourcePairing_eq_schwinger` also remains a
different anchor: it evaluates the positive common-chart Wick section
`real common edge + half-time * I`, not the source-side zero-height endpoint
`real common edge + 0 * I` pulled through `os45QuarterTurnCLE.symm`.

So the next genuine Lean obligation is not another endpoint DCT or chart
retargeting lemma.  It is a compact OS-I current transport/current contour
statement equating the source-side Figure-2-4 endpoint current with the Wick
current, equivalently the local identity

```lean
Tlocal pieceFlat = J * OS.S n pieceZD
```

for the refined compact piece.  Without that theorem, the existing local facts
correctly stop at the two different endpoint currents.

## Previous Delta

Fresh route check on May 20, 2026 16:04 CEST:

Latest exact-check log: `/tmp/osr_hdiff_current_1779285726.log`.

The ordinary refined leaf is still the genuine source-current comparison:

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

I also checked the tempting `S'_n` seed shortcut.  The existing theorem

```lean
BHW.os45CommonEdge_complexWickSeed_eqOn_of_E3
```

would be useful only after proving the Wick trace of the adjacent analytic
candidate.  For the needed candidate

```lean
fun z => BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) P.τ z)
```

that trace obligation at the ordinary Wick edge is exactly

```lean
BHW.extendF (bvt_F OS lgc n)
    (BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k))) =
  bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k)))
```

The available ordering fact `P.V_swap_ordered` normalizes back to the ordinary
Wick edge after applying the selected swap; it does not put the adjacent Wick
argument itself in the ordinary forward tube.  This matches the existing
support-file warning that the downstream `extendF ∘ permAct` branch is not the
raw `(4.12)` adjacent Wick seed.  Therefore the `S'_n` shortcut would hide the
same OS-I transport gap rather than proving it.

The remaining productive shape is unchanged: prove the compact positive
source-side current transport with the same moving side-zero weight, or an
equivalent proof that `Tlocal pieceFlat = J * OS.S n pieceZD`.

## Previous Delta

Fresh check/route correction on May 20, 2026 15:31 CEST:

Latest exact-check log: `/tmp/osr_hdiff_current_1779283307.log`.

The ordinary refined leaf is still

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

I checked the general SCV/OS boundary-value surfaces around
`tube_boundaryValueData_moving_of_fixed` and `bvt_boundary_values_moving`.
They are real-edge tube-ray moving-test theorems for arguments of the form
`x + eps • eta * I`, after a boundary functional has already been selected.
They do not compare the live OS45 source-side argument

```lean
BHW.os45FlatCommonChartSourceSide d n 1 1 eps eta u
```

with the raw Wick argument.  At `eps = 0`, that source-side path is the
interior quarter-turned point

```lean
BHW.os45QuarterTurnConfig (fun k => wickRotatePoint (u k))
```

rather than a real-edge boundary ray.  `OSToWightmanTubeIdentity` also does not
fill this gap: it upgrades a supplied distributional Wick-section equality to
pointwise equality in the forward tube, but the missing statement here is
exactly the distributional/current equality between the source-side current and
the Wick current.  The source-oriented quarter-turn corridor theorem lives on
the forbidden source-variety route and is not available for this proof.

Thus the remaining useful theorem shape is still the compact source-side
contour/current transport with the same moving side-zero weight on both
integrals; DCT, real-ray moving BV, and pointed chart overlap retargeting all
stop before this mathematical content.

## Previous Delta

Fresh exact check on May 20, 2026:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/tmp/osr_hdiff_current_1779281332.log`.  The only non-timeout hard
proof leaf remains

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

inside the ordinary refined source-current comparison.  The downstream timeout
locations are still elaboration fallout after this open leaf.

I also rechecked the nearby pre-`Hdiff` OS45 distributional/EOW surfaces.  The
proved theorem

```lean
BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick
```

compares the adjacent and ordinary *Wick* pairings against the same
cutoff-pulled source test.  It does not compare the OS45 positive source-side
current

```lean
extendF (bvt_F OS lgc n)
  (BHW.os45FlatCommonChartSourceSide d n 1 1 eps eta u)
```

with the Wick pairing.  The adjacent-pairing theorem is therefore useful later
for the Wick seed, but it is not the missing ordinary `(4.14)` side-current
transport.  The current ordinary leaf still requires a real proof of that
transport, or an equivalent proof of
`Tlocal pieceFlat = J * OS.S n pieceZD`.

## Previous Delta

The ordinary selector obstruction is now pinned to a sharper, non-chart
theorem shape.  At zero side-height the fixed source current evaluates

```lean
BHW.os45FlatCommonChartSourceSide d n 1 1 0 η0 u
  = BHW.os45QuarterTurnConfig (fun k => wickRotatePoint (u k))
```

so endpoint DCT gives the pairing of `extendF` at the quarter-turned Wick
configuration.  The Schwinger normalization instead comes from the raw Wick
pairing

```lean
bvt_F OS lgc n (fun k => wickRotatePoint (u k))
```

via `bvt_euclidean_restriction`.  These are not the same argument of the
branch function, and the quarter-turn is not being justified as a Lorentz
invariance step.  Therefore the remaining proof cannot be supplied by
`pointed_chart_integral_eventually_eq_of_seed` alone: that lemma transports
branch names only when the same approach lies in a carrier intersection.

The honest neutral lemma exposed by the current local leaf is a compact
source-side contour/current transport, in one of the following equivalent
forms:

```lean
Tendsto (fun eps =>
  ∫ u, extendF (bvt_F OS lgc n)
    (BHW.os45FlatCommonChartSourceSide d n 1 1 eps η piece u) * φ u)
  (𝓝[Set.Ioi 0] 0) (𝓝 (OS.S n φZD))
```

or, after the moving side-zero support normalization already present in the
proof,

```lean
Tendsto (fun eps => SourceMovingExtendF eps - WickMovingSide eps)
  (𝓝[Set.Ioi 0] 0) (𝓝 0)
```

A finite chart chain remains useful only after such a contour/current packet
has put neighboring integrals on the same approach and weight.  By itself it
does not prove the equality between quarter-turned Wick pairings and raw Wick
Schwinger pairings.

## Previous Delta

The ordinary source-current leaf has one further route clarification.  The flat
positive boundary family is not an independent selector for Schwinger; in the
current proof it is already pinned to the ordinary common-edge distribution
`Tlocal`:

```lean
have hflat_to_Tlocal :
    Tendsto FlatMovingSide (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tlocal pieceFlat))

have hFlatMoving_to_source :
    FlatMovingSide =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun eps => J * SourceMovingExtendF eps
```

Together these give only

```lean
have hSourceMovingExtendF_Tlocal :
    Tendsto SourceMovingExtendF (nhdsWithin 0 (Set.Ioi 0))
      (nhds (J⁻¹ * Tlocal pieceFlat))
```

while the Wick side-zero selector gives

```lean
have hpiece_sideWick_selected :
    Tendsto WickMovingSide (nhdsWithin 0 (Set.Ioi 0))
      (nhds (OS.S n pieceZD))
```

Thus any proof of

```lean
Tendsto (fun eps => SourceMovingExtendF eps - WickMovingSide eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

must genuinely prove the missing identity
`Tlocal pieceFlat = J * OS.S n pieceZD`, not derive it from the already checked
flat boundary-value theorem alone.  The coordinate calculation explains why:
the zero-height source endpoint is

```lean
(BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
  (BHW.realEmbed (BHW.os45CommonEdgeRealPoint ... u))
```

equivalently `BHW.os45QuarterTurnConfig (fun k => wickRotatePoint (u k))`.
The Wick-section theorem instead evaluates the flat point
`commonEdge + i * halfTimeDirection`, which the inverse quarter-turn sends back
to the raw Wick point.  Those are different branch arguments, so the remaining
step is exactly the OS-I current transport equating the flat/common-edge
boundary distribution with the Wick/Schwinger distribution.  A proof by
`hflat_to_Tlocal`, by endpoint DCT, or by a bare chart-chain overlap would still
be circular or would compare the wrong arguments.

## Previous Delta

The current search ruled out two tempting but non-genuine closures for the
ordinary `SourcePathMoving - WickPathMoving` leaf.

First, the existing theorem
`BHW.os45FlatCommonChart_wickSection_sourcePairing_eq_schwinger` is the
flat-chart Wick-section anchor, not the live source endpoint.  Its branch
argument is the flat point

```lean
BHW.flattenCfg n d
  (fun k mu =>
    BHW.realEmbed (BHW.os45CommonEdgeRealPoint ... u) k mu +
      (BHW.os45HalfTimeDirection ... u k mu : ℂ) * Complex.I)
```

and the flat branch then applies the inverse quarter-turn, so this is the raw
Wick value.  The live fixed/moving source current instead evaluates

```lean
BHW.extendF (bvt_F OS lgc n)
  (BHW.os45FlatCommonChartSourceSide d n 1 1 eps eta0 u)
```

whose zero-height endpoint is

```lean
(BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
  (BHW.realEmbed (BHW.os45CommonEdgeRealPoint ... u))
```

equivalently the quarter-turned Wick/common-edge endpoint.  Using the
Wick-section anchor here would silently replace the actual source current by a
different branch argument.

Second, the ordinary `(4.1)` helper
`ordinary41_fixed_test_boundaryValue_extendF` applies to standard real
boundary rays `x + eps * eta * I`.  The OS45 source-side path is the
quarter-turn pullback of a flat side-height point and has the nonzero
Figure-2-4 source endpoint above, so applying the ordinary ray theorem would
need an additional coordinate/current bridge that is not currently present.

Thus the remaining ordinary theorem should still be stated directly as a
source-side current transport, for example in the already exposed local form:

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

or equivalently through `hsource_path_gap_equiv` as

```lean
Tendsto (fun eps => SourceMovingExtendF eps - WickMovingSide eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

with the same moving side-zero weight on both integrals.  This is the genuine
missing OS-I selector; no endpoint-value shortcut or bare chart-chain overlap
has enough content to prove it.

## Previous Delta

Lean now checks the source-current-to-flat-boundary packet and exposes the
ordinary local leaf at the path-current transport rather than at the coarser
selected-limit wrapper.  In the local refined piece, the positive source-side
moving current still has the checked flat zero-height limit:

```lean
have hSourceMovingExtendF_Tlocal :
    Tendsto SourceMovingExtendF (nhdsWithin 0 (Set.Ioi 0))
      (nhds (J⁻¹ * Tlocal pieceFlat))

have hSourceMovingExtendF_gap_limit :
    Tendsto (fun eps => SourceMovingExtendF eps - WickMovingSide eps)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (J⁻¹ * Tlocal pieceFlat - OS.S n pieceZD))
```

The proof now also checks the eventual retargeting equivalence from the
`extendF`/raw Wick moving gap to the path-chart moving gap:

```lean
have hsource_path_gap_equiv :
    Tendsto (fun eps => SourceMovingExtendF eps - WickMovingSide eps)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) <->
    Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

So the remaining ordinary OS-I content is again displayed as the genuine
path-current comparison with the same moving side-zero weight:

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

This does not close the selector and deliberately does not assert a false
endpoint equality.  The checked endpoint-gap facts show exactly why: DCT still
only identifies the endpoint gap; the missing step is the local side-current
transport along the Figure-2-4 path.

Fresh exact check:
`lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean`
logged to `/tmp/osr_hdiff_current_followup_1779273313.log` exits `1`.
The ordinary unsolved goal is the displayed `SourcePathMoving - WickPathMoving`
comparison; downstream deterministic timeout diagnostics remain while this
ordinary local leaf is open.  No `sorry`, `admit`, or `axiom` occurs in Hdiff.

## Previous Delta

Lean now checks the ordinary path-to-`Aext` retargeting packet.  The moving
source path chart and moving Wick path chart have both been transported to the
same source-side weight against the explicit endpoint extension charts:

```lean
let WickA0extMoving : Real -> Complex := ...

have hSourcePath_to_A1ext_moving :
    SourcePathMoving =ᶠ[nhdsWithin 0 (Set.Ioi 0)] SourceMovingSide

have hWickPath_to_A0ext_moving :
    WickPathMoving =ᶠ[nhdsWithin 0 (Set.Ioi 0)] WickA0extMoving
```

This gives the checked equivalence:

```lean
have hpath_Aext_transport_equiv :
    Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) <->
    Tendsto (fun eps => SourceMovingSide eps - WickA0extMoving eps)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

The endpoint packet was also retargeted:

```lean
have hWickA0extMoving_selected :
    Tendsto WickA0extMoving (nhdsWithin 0 (Set.Ioi 0))
      (nhds (OS.S n pieceZD))

have hAext_moving_endpoint_gap :
    Tendsto (fun eps => SourceMovingSide eps - WickA0extMoving eps)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((∫ u, A1ext.branch (OrdSourceApproach 0 u) * piece u) -
          OS.S n pieceZD))
```

The remaining ordinary leaf is therefore no longer a bare finite-chain chart
comparison.  It is the direct local boundary-value/current transport between
the A1 endpoint branch and the A0 Wick branch with the same moving side-zero
test:

```lean
Tendsto (fun eps => SourceMovingSide eps - WickA0extMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

Fresh exact check:
`lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean`
logged to `/tmp/osr_hdiff_aext_endpoint_gap_1779267976.log` exits `1`.
The ordinary unsolved goal is the displayed A1ext/A0ext moving-current
comparison; downstream deterministic timeout diagnostics remain while this
ordinary local leaf is open.  No `sorry`, `admit`, or `axiom` occurs in Hdiff.

## Previous Delta

Lean now checks the endpoint-limit side of the remaining ordinary path-chart
comparison explicitly.  With the common moving support collar in context, the
source path chart has only its zero-height endpoint limit:

```lean
have hSourcePathMoving_endpoint :
    Tendsto SourcePathMoving (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (∫ u, (OrdPathChart cm.1).branch (OrdSourceApproach 0 u) *
          (piece : NPointDomain d n -> Complex) u))
```

The Wick path chart has the selected Schwinger limit:

```lean
have hWickPathMoving_selected :
    Tendsto WickPathMoving (nhdsWithin 0 (Set.Ioi 0))
      (nhds (OS.S n pieceZD))
```

Therefore Lean also checks the honest endpoint-gap limit:

```lean
have hpath_moving_endpoint_gap :
    Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((∫ u, (OrdPathChart cm.1).branch (OrdSourceApproach 0 u) *
          (piece : NPointDomain d n -> Complex) u) - OS.S n pieceZD))
```

This packet deliberately does not close the selector by asserting the endpoint
gap is zero.  It shows in Lean that the remaining `nhds 0` path-comparison is
exactly the missing OS-I/current transport through the Figure-2-4 corridor.

Fresh exact check:
`lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean`
logged to `/tmp/osr_hdiff_path_endpoint_gap_1779266994.log` exits `1`.
The ordinary unsolved goal is still the displayed
`SourcePathMoving - WickPathMoving` comparison; downstream deterministic
timeout diagnostics remain while this ordinary local leaf is open.

## Earlier Delta

The ordinary localized comparison has been sharpened again.  After the checked
fixed-test/moving-test source packet, terminal `extendF` normalization, and
flat side-height/Jacobian pullback, the flat side-height selector is now carried
through the distributional boundary-value theorem to the zero-height local
functional `Tlocal pieceFlat`.

```lean
have hflat_to_Tlocal :
    Tendsto FlatMovingSide (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tlocal pieceFlat))
```

This uses the real support packet `hpieceFlat_E` plus
`os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM`;
it does not assert a terminal endpoint equality.  The source/Wick support
collar was also tightened: the compact `Kpiece` now lies in
`UOrdSourcePath cm ∩ UOrdWickPath cs ∩ Usrc`, so the moving side-zero support
can be retargeted on both endpoint charts.

The checked new local chart retargeting is:

```lean
let SourcePathMoving : Real -> Complex := ...
let WickPathMoving : Real -> Complex := ...

have hSourceExtend_to_path :
    SourceMovingExtendF =ᶠ[nhdsWithin 0 (Set.Ioi 0)] SourcePathMoving

have hWickMoving_to_path :
    WickMovingSide =ᶠ[nhdsWithin 0 (Set.Ioi 0)] WickPathMoving
```

The remaining ordinary leaf is now the genuinely local chart-to-chart moving
comparison with the same moving side-zero weight:

```lean
Tendsto (fun eps => SourcePathMoving eps - WickPathMoving eps)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

A further endpoint packet is now checked in Lean:

```lean
have hpath_moving_endpoint_collar :
    forallᶠ eps in nhdsWithin (0 : Real) (Set.Ioi 0), forall u,
      u ∈ Function.support
        (((D.toSideZeroDiagonalCLM 1 1 eps eta0 pieceFlat).1 :
          SchwartzNPoint d n) : NPointDomain d n -> Complex) ->
        OrdSourceApproach eps u ∈ (OrdPathChart cm.1).carrier /\
        OrdWickApproach 0 u ∈ (OrdPathChart cs.1).carrier /\
        u ∈ P.V
```

This is the intended transport gap with the endpoint charts and common moving
support/current collar explicit.  What remains is the actual OS-I/current
transport through the Figure-2-4 path corridor; a bare finite chart chain is
still not enough without the intermediate approach/weight packets or a real
local boundary-value comparison at each approach mismatch.

Fresh exact check:
`lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean`
logged to `/tmp/osr_hdiff_endpoint_collar_1779265760.log` exits `1`.
The ordinary unsolved goal is still the displayed
`SourcePathMoving - WickPathMoving` comparison, now with
`hpath_moving_endpoint_collar` in context.  Downstream deterministic timeout
diagnostics are still present while this ordinary local leaf is open.

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

## Current Lean Delta

As of the current Hdiff frontier, the misleading endpoint-value shortcuts have
been removed from the two live selector bodies.  The remaining Lean goals are
now the fixed source-current transport statements themselves:

```lean
have hOrdPieceFixed_selected :
    Tendsto OrdPieceFixed l (nhds (OS.S n (psiOrdPieceZD a))) := by
  -- ordinary `(4.1)/(4.14)` fixed source-current transport

have hAdjPieceFixed_selected :
    Tendsto AdjPieceFixed l (nhds (OS.S n (psiAdjPieceZD a))) := by
  -- retained raw `(4.12)/(4.14)` fixed source-current transport
```

Do not reintroduce a proof obligation of the form
`terminal endpoint integral = OS.S ...`.  The checked endpoint DCTs only say
that the fixed source-current family tends to its zero-height endpoint.  The
missing OS-I step is stronger and earlier: it must identify the fixed
positive-side source current with the Schwinger value before endpoint
continuity is used.

Latest ordinary-side packet progress:

```lean
let OrdWickApproach :
    Real -> NPointDomain d n -> Fin n -> Fin (d + 1) -> Complex :=
  fun _eps u => fun k => wickRotatePoint (u k)

let OrdWickWeight : Real -> NPointDomain d n -> Complex :=
  fun _eps u => (psiOrdPieceSource a : NPointDomain d n -> Complex) u

let OrdSourceApproach :
    Real -> NPointDomain d n -> Fin n -> Fin (d + 1) -> Complex :=
  fun eps u =>
    BHW.os45FlatCommonChartSourceSide d n
      (1 : Equiv.Perm (Fin n)) (1 : Real) eps eta0 u

let OrdSourceWeight : Real -> NPointDomain d n -> Complex :=
  fun _eps u => (psiOrdPieceSource a : NPointDomain d n -> Complex) u
```

The incoming ordinary Wick edge now has the same support-aware packet shape as
the terminal edge.  A local chart `A0ext` has the same carrier as `A0a` and
branch `BHW.extendF (bvt_F OS lgc n)`, and Lean checks:

```lean
have hOrd_A0ext_A0_collar :
    forallᶠ eps in l, forall u,
      u ∈ Function.support (OrdWickWeight eps) ->
        OrdWickApproach eps u ∈ A0ext.carrier ∩ A0a.carrier

have hOrd_A0ext_to_A0_integral :
    (fun eps =>
      ∫ u, A0ext.branch (OrdWickApproach eps u) *
        OrdWickWeight eps u)
      =ᶠ[l]
    fun eps =>
      ∫ u, A0a.branch (OrdWickApproach eps u) *
        OrdWickWeight eps u

have hOrd_A0ext_wick_value :
    (∫ u, A0ext.branch (OrdWickApproach 0 u) *
      OrdWickWeight 0 u) =
    OS.S n (psiOrdPieceZD a)
```

The ordinary terminal retarget is now Lean-checked without using an endpoint
Schwinger shortcut.  A local chart `A1ext` has the same carrier as `A1a` and
branch `BHW.extendF (bvt_F OS lgc n)`.  The proof now has:

```lean
have hOrd_A1ext_A1_collar :
    forallᶠ eps in l, forall u,
      u ∈ Function.support (OrdSourceWeight eps) ->
        OrdSourceApproach eps u ∈ A1ext.carrier ∩ A1a.carrier

have hOrd_A1ext_to_A1_integral :
    (fun eps =>
      ∫ u, A1ext.branch (OrdSourceApproach eps u) *
        OrdSourceWeight eps u)
      =ᶠ[l]
    fun eps =>
      ∫ u, A1a.branch (OrdSourceApproach eps u) *
        OrdSourceWeight eps u

have hOrd_A1ext_endpoint_bvt :
    (∫ u, A1ext.branch (OrdSourceApproach 0 u) *
      OrdSourceWeight 0 u) =
    ∫ u, bvt_F OS lgc n (OrdSourceApproach 0 u) *
      OrdSourceWeight 0 u

have hOrd_A1ext_endpoint_flat_zero :
    (∫ x,
      BHW.os45FlatCommonChartBranch d n OS lgc
        (1 : Equiv.Perm (Fin n)) (fun j => (x j : Complex)) *
      psiOrdPieceFlat a x) =
    J * ∫ u, A1ext.branch (OrdSourceApproach 0 u) *
      OrdSourceWeight 0 u

have hOrd_A1ext_endpoint_Tlocal :
    J * ∫ u, A1ext.branch (OrdSourceApproach 0 u) *
      OrdSourceWeight 0 u =
    Tlocal (psiOrdPieceFlat a)

have hOrdPieceFixed_scaled_Tlocal :
    Tendsto (fun eps => J * OrdPieceFixed eps) l
      (nhds (Tlocal (psiOrdPieceFlat a)))

have hFlatOrd_piece_selected_Tlocal :
    Tendsto (FlatOrdPiece a) l
      (nhds (Tlocal (psiOrdPieceFlat a)))
```

The old center-only terminal-left collar is intentionally not the next target:
it does not control the support of the source-current integral.  The remaining
ordinary gap is now sharper: the localized fixed ordinary piece has been
selected to the ordinary edge CLM, so the missing normalization is the genuine
piece-level equality

```lean
Tlocal (psiOrdPieceFlat a) = J * OS.S n (psiOrdPieceZD a)
```

This equality still has to come from the real OS-I/Wick-anchor transport, not
from the zero-height endpoint DCT alone.  If the route proceeds by the finite
chart chain, the relevant positive-side approaches and weights still need
support-aware edge packets.

Current ordinary-side source-cover progress:

```lean
have hOrd_source_path_cover_inter_zero_support :
    ∀ u ∈ tsupport (ψOrdPieceSource a : NPointDomain d n -> Complex),
      ∃ c : KOrdPath,
        c ∈ sOrdPath ∧
          OrdSourceApproach 0 u ∈
            (OrdPathChart c).carrier ∩ A1ext.carrier

let αOrdSourcePath := sOrdPath
let UOrdSourcePath : αOrdSourcePath -> Set (NPointDomain d n) := fun c =>
  {u | OrdSourceApproach 0 u ∈
    (OrdPathChart c.1).carrier ∩ A1ext.carrier}

have hOrd_source_path_cover_zero_tsupport :
    tsupport (ψOrdPieceSource a : NPointDomain d n -> Complex) ⊆
      ⋃ c : αOrdSourcePath, UOrdSourcePath c

have hOrdPathChart_model :
    ∀ z : KOrdPath,
      Set.EqOn (OrdPathChart z).branch
        (BHW.extendF (bvt_F OS lgc n))
        (OrdPathChart z).carrier

have hOrd_source_zero_support_branch_witness :
    ∀ u,
      u ∈ Function.support (OrdSourceWeight 0) ->
        ∃ c : αOrdSourcePath,
          u ∈ UOrdSourcePath c ∧
            A1ext.branch (OrdSourceApproach 0 u) =
              (OrdPathChart c.1).branch (OrdSourceApproach 0 u)

have hOrd_source_path_piece_collar :
    ∀ c : αOrdSourcePath,
      ∀ w : SchwartzNPoint d n,
        HasCompactSupport (w : NPointDomain d n -> Complex) ->
        tsupport (w : NPointDomain d n -> Complex) ⊆ UOrdSourcePath c ->
        ∀ᶠ eps in l, ∀ u,
          u ∈ Function.support (w : NPointDomain d n -> Complex) ->
            OrdSourceApproach eps u ∈
              (OrdPathChart c.1).carrier ∩ A1ext.carrier

have hOrd_A1ext_to_pathChart_piece_integral :
    ∀ c : αOrdSourcePath,
      ∀ w : SchwartzNPoint d n,
        HasCompactSupport (w : NPointDomain d n -> Complex) ->
        tsupport (w : NPointDomain d n -> Complex) ⊆ UOrdSourcePath c ->
        (fun eps =>
          ∫ u, A1ext.branch (OrdSourceApproach eps u) * w u)
          =ᶠ[l]
        fun eps =>
          ∫ u, (OrdPathChart c.1).branch
            (OrdSourceApproach eps u) * w u
```

This is the honest compact-local split point for the ordinary selector: the
source support is now covered by finite chart preimages at zero height, with
the terminal `A1ext` carrier included.  The latest checked increment also
names the common-model fact for every finite path chart and turns the cover
into an actual support-level branch witness: on every zero-height source
support point, `A1ext.branch` agrees with the witnessed path-chart branch at
the same approach.  It also now has the fixed-chart positive-side collar:
any future localized source test supported in a chosen `UOrdSourcePath c`
has its moving positive-side approach eventually inside the same
`OrdPathChart c/A1ext` overlap.  Finally, this collar is consumed in the first
scalar edge-integral transport: for such a localized source test, the
`A1ext` integral and the selected path-chart integral are eventually equal
with the same approach and weight.

A full source-piece Schwartz partition subordinate to these preimages was
tested in the live theorem body.  Even when compressed into a single
existential packet, carrying the partition construction through the giant
proof context caused deterministic downstream elaboration timeouts.  The next
implementation should either consume such a partition in a helper whose
exported result is a scalar edge-integral equality, or build the first
positive-side edge packet directly from the support-level witness and
fixed-chart collar above.  The latter now exists for the `A1ext -> OrdPathChart`
retarget; the next missing part is producing/consuming the localized source
pieces without carrying the raw partition construction through the whole
theorem body.

Latest Lean delta: the neutral helper
`exists_finite_schwartz_smul_partition_on_tsupport` now packages the finite
Schwartz source partition produced by a finite open cover of a compact
topological support.  Re-consuming that helper directly inside
`hOrdPieceFixed_selected` again typechecked locally but reintroduced
downstream elaboration timeouts, so the in-body use was backed out.  The
helper should next be consumed by a slimmer scalar-transport helper whose
result does not keep the raw partition witnesses in the producer context.

Latest incremental helper: `sourceSide_integral_eventually_eq_sum_chart_partition`
now performs that scalar transport outside the giant producer context.  It
packages a finite Schwartz partition subordinate to source-side carrier
preimages, proves eventual integrability for both chart branches, splits the
original source integral into the finite localized sum, and uses the supplied
overlap `EqOn` plus the moving support collar to transport the sum to the
neighboring chart branches.  A direct one-line consumption of this helper
inside `hOrdPieceFixed_selected` was also tested; the theorem itself checks,
but even the compact existential packet still causes downstream elaboration
timeouts when kept in the open producer context.  Do not keep that local
packet until the ordinary selector proof is reorganized so the packet is
consumed immediately inside a completed subproof.

The final common-edge endpoint algebra is now discharged by the small local
folding lemma
`commonEdge_pulledRealBranch_sub_eq_zero_of_extendF_perm_eq`; this removes the
previous strict-heartbeat timeout at the terminal `rw`/`change` without
changing the mathematical selector frontier.

Fresh exact check:

```bash
lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/tmp/osr_hdiff_endpoint_helper_1779252829.log`.

Result: exit code `1`, with only the two intended selector unsolved goals at
`Hdiff.lean:5106:64` and `Hdiff.lean:7978:58`; no timeout diagnostics.

Fresh exact check after the top-level scalar transport helper:

```bash
lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/tmp/osr_hdiff_toplevel_only_1779254354.log`.

Result: exit code `1`, with only the two intended selector unsolved goals at
`Hdiff.lean:5308:64` (`hOrdPieceFixed_selected`) and `Hdiff.lean:8180:58`
(`hAdjPieceFixed_selected`); no timeout diagnostics.

For the finite chain, branch equality on overlaps is useful only when the two
neighboring chart integrals have first been put into the same local
side-height coordinates on a support collar.  A bare chain of pointed charts
and seeds does not by itself compare different approach families.  Each step
must therefore provide:

```lean
have hleft_to_edge :
    I_left =ᶠ[l]
      fun eps => ∫ x, A.branch (edgeApproach eps x) * edgeWeight eps x

have hright_to_edge :
    I_right =ᶠ[l]
      fun eps => ∫ x, B.branch (edgeApproach eps x) * edgeWeight eps x

have hedge_collar :
    ∀ᶠ eps in l, ∀ x,
      x ∈ Function.support (edgeWeight eps : X -> Complex) ->
        edgeApproach eps x ∈ A.carrier ∩ B.carrier
```

Only after these three facts are in place may
`PointedMetricBranchChart.eqOn_inter_of_seed` turn the overlap seed into
equality of the two edge integrals.  If two adjacent slots naturally use
different local approaches, insert the local boundary-value/DCT comparison
there; do not hide the mismatch behind `eventual_eq`.

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

## Latest Common-Partition Packet

The frontier now has the checked static Wick-endpoint packet
`fixedApproach_integral_eq_sum_chart_partition` and the stronger paired packet
`fixed_sourceSide_integral_common_chart_partition`.

The paired packet chooses one finite Schwartz partition subordinate to a
single common open cover and proves both:

```lean
∫ Astatic.branch (staticApproach u) * w u
  =
∑ c, ∫ (Bstatic c).branch (staticApproach u) * piece c u
```

and

```lean
(fun eps =>
  ∫ Amoving.branch (sourceSide eps u) * w u)
  =ᶠ[l]
fun eps =>
  ∑ c, ∫ (Bmoving c).branch (sourceSide eps u) * piece c u
```

This is the non-mismatched endpoint transport shape needed for the ordinary
selector: the Wick retargeting and source-side retargeting can now share the
same localized pieces after a common refinement of their carrier preimages.

A body-level attempt to retain the ordinary common-refinement facts inside
`hOrdPieceFixed_selected` checked locally but reintroduced deterministic
downstream elaboration timeouts.  It was backed out.  The next implementation
should consume `fixed_sourceSide_integral_common_chart_partition` only inside a
completed selector subproof whose exported result is the limit statement, not
as extra persistent local data in the open producer context.

Fresh exact check:

```bash
lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/tmp/osr_hdiff_common_partition_stable_1779258600.log`.

Result: exit code `1`, with only the two intended selector goals at
`Hdiff.lean:5717:64` (`hOrdPieceFixed_selected`) and `Hdiff.lean:8589:58`
(`hAdjPieceFixed_selected`); no timeout diagnostics.

Follow-up refinement: `fixed_sourceSide_integral_refined_chart_partition` now
takes separate finite Wick-endpoint and source-endpoint chart covers and
constructs the product common refinement internally.  This avoids materializing
the product cover in the giant theorem context.  Its output pieces are indexed
by `α × β`, supported in `Ustatic α ∩ Umoving β`, and carry both retargeted
endpoint equations against those same pieces.

Fresh exact check after this refinement:

```bash
lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/tmp/osr_hdiff_refined_partition_1779260400.log`.

Result: exit code `1`, with only the two intended selector goals at
`Hdiff.lean:5813:64` (`hOrdPieceFixed_selected`) and `Hdiff.lean:8685:58`
(`hAdjPieceFixed_selected`); no timeout diagnostics.

Latest limit-level refinement: `fixed_sourceSide_integral_refined_chart_partition_tendsto_of_local`
now consumes the refined product partition internally and exports the actual
limit transport.  Its remaining premise is the honest localized comparison:
for every product-refined piece supported in `Ustatic cs ∩ Umoving cm`, the
source-side branch integral in chart `Bmoving cm` must tend to the static Wick
integral in chart `Bstatic cs`.  Under that premise, the helper proves the
whole `Amoving` source-side integral tends to the whole `Astatic` Wick
integral, using the same partition pieces for both sides and then summing the
localized limits.

This pins the next mathematical gap more sharply: partition construction,
support collars, integrability, and chart retargeting are now checked outside
the giant producer context.  What remains for the ordinary selector is the
localized boundary-value comparison on each refined support piece.

Fresh exact check after the limit-level refinement:

```bash
lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/tmp/osr_hdiff_limit_refinement_1779265000.log`.

Result: exit code `1`, with only the two intended selector goals at
`Hdiff.lean:5915:64` (`hOrdPieceFixed_selected`) and `Hdiff.lean:8787:58`
(`hAdjPieceFixed_selected`); no timeout diagnostics.

## 2026-05-22 Selected-Data Hdiff Tail Splice

The selector leaf is no longer the intended production surface for the final
Hdiff germ.  I added and checked:

```lean
BHW.os45_hdiff_of_flat_seed
BHW.os45_hdiff_of_selectedJostData
```

in `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean`.

`os45_hdiff_of_flat_seed` isolates the already-checked post-seed tail of
`BHW.os45CommonEdge_localFigure24DifferenceGerm_of_OSI45`: given the connected
local initial-sector `EqOn` seed at the flat common edge, the `S'_n` machinery
produces the zero Hdiff germ and the common-edge adjacent-minus-ordinary trace.

`os45_hdiff_of_selectedJostData` composes the faithful selected
Jost/Ruelle packet with that tail: it takes
`SelectedAdjacentDistributionalJostAnchorData` plus adjacent ET-overlap
connectedness, builds the flat seed via
`BHW.os45_flat_seed_of_selectedJostData`, and returns the local Hdiff germ
directly.  This is the replacement route for the old individual fixed-selector
attempt; it still leaves the honest producers as selected Jost anchor data and
adjacent overlap connectedness.

Verification:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean
lake env lean test/proofideas_os45_hdiff_from_flat_seed.lean
```

Both exit code `0`.

The current Hdiff production file was updated to consume
`BHW.os45_hdiff_of_flat_seed` after its existing `hflat_seed` construction,
removing the duplicated downstream `S'_n` tail.  A fresh exact Hdiff check:

```bash
lake env lean -DmaxHeartbeats=1200000 OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Figure24Hdiff.lean
```

Log: `/tmp/osr_hdiff_tail_seed_1779424392.log`.

Result: exit code `1`.  The ordinary selector is still the first unsolved goal
at `Hdiff.lean:5978:64`; the adjacent selector region still times out under
the old selector route.  The new selected-data theorem in `OSToWightmanRuelleOverlap.lean`
is the checked route that bypasses that individual-selector surface.

## 2026-05-22 Local Edge-Pairing Hdiff Surface

Following the blueprint/test-file discipline, I first added and checked
`test/proofideas_os45_hdiff_local_edge_pairing.lean`.  It verifies the
one-edge Ruelle splice:

```lean
BHW.proofideas_bvt_F_extendF_adjacent_overlap_of_localEdgePairing
BHW.proofideas_os45_ruelle_commonEdge_boundary_hint_of_localEdgePairing
BHW.proofideas_os45_flat_seed_of_localEdgePairing
BHW.proofideas_os45_hdiff_of_localEdgePairing
```

The production promotion lives in
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean`
as:

```lean
BHW.bvt_F_extendF_adjacent_overlap_of_localEdgePairing
BHW.os45_ruelle_commonEdge_boundary_hint_of_localEdgePairing
BHW.os45_flat_seed_of_localEdgePairing
BHW.os45_hdiff_of_localEdgePairing
BHW.os45_hdiff_of_compactWickPairingEq
```

This removes an overlarge theorem surface from the replacement route.  The
local OS45 Hdiff germ now only requires the one adjacent overlap connectedness
for `P.τ` and one compact real-open edge pairing packet.  It no longer needs
global `SelectedAdjacentDistributionalJostAnchorData` for every adjacent swap
when proving a single Figure-2-4 local patch.

`BHW.os45_hdiff_of_compactWickPairingEq` then consumes the existing
one-adjacent-swap `OS45CompactFigure24WickPairingEq` packet directly, using
the identity-labelled compact real patch as the local edge witness.  The
remaining producer is therefore concrete: prove the single compact
Figure-2-4 Wick pairing plus connectedness of the single adjacent overlap.

Verification:

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanRuelleOverlap.lean
lake build OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap
lake env lean test/proofideas_os45_hdiff_local_edge_pairing.lean
```

All three exit code `0` (the scratch file has only unused-section-variable
warnings).  No `sorry`/`admit`/`axiom` was introduced.  A pinned Deep Research
interaction for the remaining adjacent-overlap geometry is running as
`v1_ChdpOTRQYXRDZUZKamtuc0VQZ28yVnNRaxIXaTk0UGF0Q2VGSmprbnNFUGdvMlZzUWs`.

## 2026-05-24 Reduced Local Same-Boundary Consumer

The current theorem-2 locality route no longer treats the old fixed selector
as the primary proof surface.  The reduced bridge now has a checked production
consumer for the faithful local Ruelle/EOW packet:

```lean
reduced_local_comparison_of_sameBoundaryCLM
reducedAfterSwap_tendsto_of_local_tsupport_cover
reducedAfterSwap_tendsto_of_local_sameBoundaryCLM_cover
reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_local_sameBoundaryCLM
```

in

```text
OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanReducedFiberMarginalSchwartz.lean
```

The theorem says that `ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz`
follows from a pointwise local packet: around every point of the compact
reduced support, the canonical reduced branch and the adjacent-after-swap
reduced branch must converge, on tests supported in that local real
neighborhood, to the same boundary-value CLM.  The finite Schwartz partition
of unity and the reduced adjacent change of variables are now part of the
checked substrate.

Verification:

```bash
lake env lean -DmaxHeartbeats=1200000 \
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanReducedFiberMarginalSchwartz.lean
lake env lean -DmaxHeartbeats=1200000 \
  test/proofideas_reduced_local_eow_to_global.lean
```

Both exit code `0`; targeted scan on those files reports no
`sorry`/`admit`/`axiom`, and `git diff --check` passes.

This sharpens the remaining analytic leaf.  To close the theorem-2 locality
sorry via the reduced route, the next proof body must construct that local
same-boundary CLM packet from the Jost/Ruelle/OS-I argument near each
adjacent-spacelike reduced support point.  The separate nonzero-support versus
strict-`tsupport` boundary passage remains isolated in the scratch theorem
`proofideas_adjacent_locality_of_strict_tsupport_locality_and_zeroOff_exhaustion`.
