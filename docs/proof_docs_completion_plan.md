# Proof-Docs Completion Plan

Purpose: this note is the execution plan for bringing the proof-document stack
to the standard

> "Lean implementation should require proving the named packages, not
> rediscovering the mathematics, changing theorem surfaces, or making new route
> choices."

This is a documentation-only plan. It does **not** authorize production Lean
deviation from the existing blueprints.

This note should be read together with:

- `docs/sorry_triage.md`
- `docs/mathlib_gap_analysis.md`
- `docs/theorem2_locality_blueprint.md`
- `docs/theorem3_os_route_blueprint.md`
- `docs/theorem4_cluster_blueprint.md`
- `docs/general_k_continuation_blueprint.md`
- `docs/scv_infrastructure_blueprint.md`
- `docs/gns_pipeline_blueprint.md`
- `docs/nuclear_spaces_blueprint.md`
- `docs/vna_infrastructure_blueprint.md`

Current theorem-2 BHW correction: earlier text in these documents sometimes
used "fixed-`w` chamber route" for two different objects.  The common
fixed-`w` permuted-forward-tube gallery is rejected, because distinct ordinary
permuted forward-tube sectors are disjoint.  The reachable-label `hOrbit`
theorem `petOrbitChamberConnected_of_two_le` is weaker than that rejected
common-witness gallery, but it is still an additional pointwise
complex-Lorentz-orbit stratification theorem.  It is not the strict OS-paper
implementation gate for theorem 2.  Gemini Deep Research interaction
`v1_ChZjT1h1YWRpZUU1LThfdU1QMi1LRGVBEhZjT1h1YWRpZUU1LThfdU1QMi1LRGVB`
confirmed this theorem-shape correction: `hOrbit` should be documented as an
extra custom geometric theorem if pursued, while the faithful OS I §4.5 route
targets direct source-backed BHW single-valuedness on `S''_n`.

Locality API correction gate, 2026-05-07: before any Lean refactor responding
to GitHub issue #83, the proof-doc decision is fixed as follows.  The OS I/OS
II R3 surface used by theorem 2 is adjacent local commutativity: swap
neighboring arguments `i` and `i+1` under the adjacent spacelike-support
hypothesis.  This is the statement already carried by
`bvt_W_swap_pairing_of_spacelike`, and it is the only locality theorem that the
current E→R route is proving.  The implementation may rename the current
predicate surface to `IsAdjacentLocallyCommutativeWeak` and update consumers so
the API no longer suggests an arbitrary-pair theorem.  It may also keep a
documented compatibility alias for the standard adjacent predicate if a
transition step needs it.

The implementation must **not**:

- restore the old arbitrary-pair predicate as the public `WightmanFunctions`
  locality field;
- introduce an adjacent→arbitrary locality theorem as an axiom, sorry, or
  hidden assumption;
- use any QFT-specific locality upgrade as an axiom-gate workaround.

If an arbitrary pair-swap property is useful later, it must be separately named
as a stronger non-frontier predicate and related to the adjacent predicate only
by the safe direction pair-swap → adjacent.  No theorem-2 Lean work may depend
on the stronger property.

Current theorem-2 implementation ledger: the downstream Hall-Wightman/Jost
source package remains the route after the local OS45 envelope has been
constructed, but it is not the immediate Lean gate.  The immediate gate is
local Slot 1:

1. keep the checked bounded identity-order perturbation and raw real-open ball
   selector as support;
2. checked: `BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability`
   and `BHW.os45_adjacent_identity_horizontalEdge_sourcePatch` now choose the
   ordered seed inside `Ufig ∩ Upath`, shrink with compact closure, and export
   the closure-level Figure-2-4 path field;
3. current proof-document frontier: finish the upstream direct OS-I compact
   branch-difference producer and the scalar-source inputs before any
   branch-local Lean pass:
   `BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45`
   must be proved as a direct OS I §4.5 / BHW-Jost compact theorem, feeding
   `BHW.OS45CompactFigure24WickPairingEq` and
   the checked ordinary source anchors
   `BHW.sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq`
   and
   `BHW.bvt_F_distributionalJostAnchor_of_compactWickPairingEq`;
   the first carrier/algebra layer for the direct BHW/Jost proof is now
   checked as `BHW.OS45SourcePatchBHWJostHullData`,
   `BHW.os45_sourcePatch_bhwJostHullData_on_figure24SourcePatch`,
   `BHW.OS45SourcePatchBHWJostHullData.U_isPathConnected`,
   `BHW.OS45SourcePatchBHWJostPairData`,
   `BHW.continuous_wickRotateRealConfig`,
   `BHW.differentiable_permAct`,
   `BHW.isOpen_permAct_preimage_extendedTube`,
   `BHW.differentiableOn_extendF_bvt_F_extendedTube`,
   `BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube`,
   `BHW.wickRotate_mem_BHW_forwardTube_of_ordered`,
   `BHW.extendF_bvt_F_wickRotate_eq_of_ordered`,
   `BHW.OS45SourcePatchBHWJostHullData.wick_id_forwardTube_of_ordered`,
   `BHW.OS45SourcePatchBHWJostOrientedContinuationInputs`,
   `BHW.OS45SourcePatchBHWJostOrientedContinuationInputs.exists_gluedBranch`,
   `BHW.OS45SourcePatchBHWJostHullData.exists_ordinaryBranch_of_orientedContinuationInputs`,
   `BHW.OS45SourcePatchBHWJostHullData.exists_adjacentBranch_of_orientedContinuationInputs`,
   `BHW.OS45SourcePatchBHWJostHullData.ordinaryBranchOfOrientedContinuationInputs`,
   `BHW.OS45SourcePatchBHWJostHullData.adjacentBranchOfOrientedContinuationInputs`,
   `BHW.OS45SourcePatchBHWJostHullData.pairDataOfOrientedContinuationInputs`,
   `BHW.integrable_bvt_F_wickRotate_mul_schwartz_of_orderedSector`,
   `BHW.integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector`,
   `BHW.integrable_extendF_realSource_mul_schwartz_of_ET`,
   `BHW.integrable_wickEdge_bvt_F_mul_schwartz_on_figure24SourcePatch`,
   `BHW.integrable_extendF_realSource_mul_schwartz_on_figure24SourcePatch`,
   `BHW.integrable_extendF_swapRealSource_mul_schwartz_on_figure24SourcePatch`,
   `BHW.integral_wickBranchDifference_mul_eq_zero_of_pairing_eq`,
   `BHW.os45_wickBranchDifference_zero_of_euclideanEdge_pairing_eq_on_timeSector`,
   `BHW.OS45SourcePatchBHWJostPairData.restrict`,
   `BHW.OS45SourcePatchBHWJostPairData.restrict_figure24SourcePatch`,
   `BHW.OS45SourcePatchBHWJostPairData.ofHullDataAndBranches`,
   `BHW.OS45SourcePatchBHWJostPairData.difference`,
   `BHW.OS45SourcePatchBHWJostPairData.difference_holo`,
   `BHW.OS45SourcePatchBHWJostPairData.difference_wick_trace`,
   `BHW.OS45SourcePatchBHWJostPairData.difference_real_trace`, and
   `BHW.os45_pairData_difference_identity_of_wickDistributionZero`,
   `BHW.os45_pairData_difference_realTrace_zero_of_wickDistributionZero`,
   `BHW.realSourceBranchDifference_zero_of_pairData_difference_zero`, and
   `BHW.integral_realSourceBranchDifference_eq_zero_to_pairing_eq`,
   with the checked source-patch/compact-packet bridges
   `BHW.os45Figure24_sourcePatch_pairing_eq_of_realSourceBranchDifference_zero`
   and
   `BHW.os45CompactFigure24WickPairingEq_of_realSourceBranchDifference_zero`,
   plus the checked carrier-consumer bridge
   `BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero`
   and its canonical-integrability variant
   `BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero_canonical`
   and the full-family consumers
   `BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero`
   / `BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero_canonical`
   and
   `BHW.bvt_F_distributionalJostAnchor_of_pairData_difference_zero`
   / `BHW.bvt_F_distributionalJostAnchor_of_pairData_difference_zero_canonical`;
   the exact-source-patch consumers
   `BHW.os45CompactFigure24WickPairingEq_of_pairData_on_figure24SourcePatch`
   and
   `BHW.bvt_F_distributionalJostAnchor_of_pairData_on_figure24SourcePatch`
   reduce the remaining canonical route input to a full adjacent family of
   pair carriers built directly on `BHW.os45Figure24SourcePatch`;
   the oriented adjacent real-seed/anchor layer remains a downstream
   determinant-regular shrinking step;
   it must not use `BHW.os45_adjacent_commonBoundaryEnvelope`, the oriented
   branch-germ suppliers, PET independence, final locality, or the later
   Jost/Ruelle boundary package; then finish the active
   proper-complex/oriented representative
   `BHW.sourceOrientedScalarRepresentativeData_bvt_F` through
   `BHW.sourceFullFrameDet_*`,
   `BHW.same_sourceOrientedInvariant_detOneOrbit_or_singularLimit`,
   `BHW.extendedTube_same_sourceOrientedInvariant_extendF_eq`,
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected`,
   whose topology split is now checked by
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected_of_localRealization`,
   `BHW.sourceOrientedVarietyGermHolomorphicOn_extendF_descent`,
   `BHW.sourceOrientedScalarRepresentativeData_of_branchLaw`, and
   `BHW.hallWightman_sourceOrientedScalarRepresentativeData`; and the
   oriented adjacent `S'_n` package
   `BHW.os45AdjacentSPrimeOrientedScalarizationChart_of_figure24`,
   `BHW.os45AdjacentSPrimeOrientedSourceEq_of_compactWickPairingEq`,
   `BHW.os45AdjacentSPrimeOrientedScalarSeed_of_compactWickPairingEq`,
   `BHW.os45AdjacentSPrimeOrientedSeedFigure24Path`, and
   `BHW.os45AdjacentSPrimeOrientedSeedFigure24Path_of_compactWickPairingEq`,
   plus the oriented local source/branch compatibility names recorded in the
   theorem-2 blueprint;
4. only after those scalar-source inputs are proof-ready may the branch-local
   source-germ layer be implemented through the oriented scalar-packet
   surfaces
   `BHW.os45OneBranchOrientedSourceEq_sourceInput_id`,
   `BHW.os45OneBranchOrientedSourceEq_sourceInput_adjacent`,
   `BHW.os45OneBranchOrientedACRBHWAgreement_sourceInput`,
   `BHW.os45OneBranchOrientedACRBHWAgreement_of_sourcePatch`,
   `BHW.os45BranchHorizontalSourceGermAt_of_orientedSourceEq`,
   `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_id`,
   `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_adjacent`,
   `BHW.os45SPrime_figure24LocalOrientedSourceEq_of_BHWJost`, and
   `BHW.os45SPrime_figure24LocalOrientedBranchCompatibility_of_BHWJost`.
   The old pure-Gram names are archived as conditional side surfaces only if
   a full-component Hall-Wightman source theorem is separately supplied;
5. construct the identity and adjacent branch BV packets, subtract them, and
   call the checked one-chart local EOW/gluing route to produce
   `BHW.os45_adjacent_commonBoundaryEnvelope`.

Only after this Slot 1 envelope exists does the route move to
`bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII`, the checked
projection to `BHW.SourceDistributionalAdjacentTubeAnchor`, the direct source
frontier `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
and then the `S''_n` single-valuedness/Jost boundary-transfer layer.  This
downstream package is still the alternative to BHW/PET monodromy through
`hOrbit`; it must not be used to manufacture the local source-germ or EOW
inputs.

Readiness status for the active scalar-source route (2026-05-02):
**proof-doc route pinned; public wrapper Lean not ready**.  The proof
documents now expose the correct proper-complex/oriented theorem surfaces, and
the pure-Gram orientation/improper-component gate is explicit.  The active
lower producer groups have implementation-level transcripts, so a future Lean
pass has legitimate first targets inside the named finite-dimensional, SCV, or
OS-I support lemmas.  This does **not** make the public constructors
`BHW.sourceOrientedScalarRepresentativeData_bvt_F`, the oriented adjacent
`S'_n` package, or the oriented branch-local source-germ layer valid first
targets.  Those public surfaces may be assembled only after their lower
producers are proved in Lean or replaced by already implemented sorry-free
support theorems with the same mathematical content.  The paper-source audit
separates Hall-Wightman's scalar-product theorem from OS I Section 4.5's
proper-complex `L_+(C)` continuation formulation; theorem 2 now follows the
latter, so `BHW.sourceScalarRepresentativeData_bvt_F` is not an active Lean
target unless a separate full-component source-import decision is made.

Latest readiness refinement, 2026-05-02: the oriented identity-principle
subroute has an implementation-level transcript, including the max-rank
connectedness/density conversions, complex max-rank chart propagation, and the
continuity closure step.  The later proof-doc pass also pinned the
implementation transcripts for the lower five source groups listed below.
This does **not** open the public scalar-representative or adjacent wrapper
theorems yet: these groups are now documented as mathematical proof
obligations with named support lemmas, but they are not implemented or
verified in Lean.

Latest source-patch refinement, 2026-05-03: the strict OS I §4.5
BHW/Jost source-patch theorem is still **not** ready for production Lean at
the public wrapper.  The docs now reject the false generic extension claim
"open subset meets connected hull, therefore extends."  The real first Lean
targets are the exposed exponential near-identity support, the local invariant
continuation chart on the starting sector, the one-step overlap continuation
theorem, and the compact-path continuation-chain/atlas producer.  In the
conditional ordinary fork this is the scalar-product chart; in the strict
route it is the oriented source-invariant chart.  The one-step theorem now
has an explicit chart-branch descent
surface using `branch_same_sourceGram` in the conditional ordinary fork and
`branch_same_sourceOrientedInvariant` in the strict fork, together with
`branch_complexLorentzInvariant`;
the compact-path theorem is pinned to Mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval`; and chain
single-valuedness is split through a genuine Hall-Wightman/Jost closed-loop
monodromy theorem.  The chain carrier now fixes one base point
`p0 ∈ Ω0 ∩ U` and stores `p0 ∈ start_patch`, so two-chain comparison and
closed-loop monodromy have a real common normalization patch rather than an
anonymous nonempty initial overlap.  Local chart carriers and invariant-domain
patches are also required to be preconnected, because the identity theorem
cannot silently jump between components of an open chart.  The compact-path
layer now uses explicit branch-free transfer packages, so the finite
subdivision cover is chosen from geometry neighborhoods rather than from
already-constructed continuation chains; in the strict fork these are
`BHW.BHWJostOrientedBranchFreeTransferNeighborhood`,
`BHW.BHWJostOrientedSourceNormalFormGeometryPatch`, and
`BHW.bhw_jost_uniformOrientedDescent_on_sourceNormalFormPatch`.  The
closed-loop monodromy surface now carries local invariant charts, transition
data, and a closing invariant patch, reducing the source-level equality to
`BHW.bhw_jost_closedChain_orientedMonodromy_trivial` in the strict route.
The plain-Gram version is now explicitly conditional on the
full-component Hall-Wightman source input recorded in the paper-source audit
below.  Proper-complex `L_+(C)` invariance alone does not justify
`branch_same_sourceGram` in scalar rank `d + 1`; in the strict OS I §4.5
route the same continuation-chain/closed-loop architecture must be ported to
the oriented source invariant, with determinant coordinates replacing the
plain rank-exact Gram monodromy surface.  Only after either that oriented
strict-route packet is proof-ready, or the full-component Hall-Wightman input
is formally adopted with exact parameters, may
`BHW.os45_sourcePatch_bhwJostPairData_on_figure24SourcePatch_of_OSI45` be
assembled.

Current Lean checkpoint, updated 2026-05-06: production Lean has now started
below the public wrapper at both the lower oriented carrier/API layer and the
direct BHW/Jost pair-data algebra layer.  The checked file
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedContinuation.lean`
adds the OS45 source-patch ambient/hull, the one-way oriented invariant union
domain, the checked `UnitIntervalOrderedSubdivision` wrapper around Mathlib's
open-cover subdivision theorem, endpoint cover helpers
`BHW.UnitIntervalOrderedSubdivision.interval_endpoints_mem_cover`,
`BHW.UnitIntervalOrderedSubdivision.left_endpoint_mem_cover`,
`BHW.UnitIntervalOrderedSubdivision.right_endpoint_mem_cover`, and the
path-specialized selector
`BHW.unitInterval_orderedSubdivision_of_path_openCover`; the branch-free
transfer cover is specialized as
`BHW.exists_unitInterval_orderedSubdivision_of_orientedTransferCover`,
`BHW.unitInterval_orderedSubdivision_of_orientedTransferCover`, and
`BHW.orientedTransferSubdivision_interval_endpoints_mem`.  The file also adds
the checked open preconnected neighborhood shrinker, `SourceOrientedMaxRankAt`,
the exceptional-rank bridges
`BHW.sourceOrientedExceptionalRank_iff_not_maxRank` and
`BHW.not_sourceOrientedExceptionalRank_iff_maxRank`,
the oriented local chart/transition/chain/closed-loop/atlas carriers, and
mechanical descent helpers from oriented germ equality to source-branch
equality.  The realization fields are now
operational in checked Lean through
the local chart provenance field
`BHW.BHWJostLocalOrientedContinuationChart.carrier_is_lorentz_step`,
`BHW.BHWJostLocalOrientedContinuationChart.exists_source_realization_branch_eq`,
`BHW.BHWJostLocalOrientedContinuationChart.exists_source_realization_mem_U_branch_eq`,
`BHW.BHWJostOrientedTransitionData.sourcePatch_subset_U`,
`BHW.BHWJostOrientedTransitionData.source_mem_U`,
`BHW.BHWJostOrientedTransitionData.source_mem_right_carrier`,
`BHW.BHWJostOrientedTransitionData.target_mem_overlap`,
`BHW.BHWJostOrientedTransitionData.target_mem_left_carrier`,
`BHW.BHWJostOrientedTransitionData.source_branch_agree_at_source`,
`BHW.BHWJostOrientedTransitionData.source_branch_agree_at_target`,
`BHW.BHWJostOrientedTransitionData.symm`,
`BHW.BHWJostOrientedTransitionData.exists_sourcePatch_realization_of_orientedPatch`,
`BHW.BHWJostOrientedTransitionData.exists_sourcePatch_realization_mem_U_of_orientedPatch`,
`BHW.BHWLocalChartTerminalComparisonData`,
`BHW.BHWLocalChartTerminalComparisonData.branch_eq_at_endpoint`,
`BHW.BHWLocalChartTerminalComparisonData.symm`,
`BHW.BHWLocalChartTerminalComparisonData.trans`,
`BHW.BHWLocalChartTerminalComparisonData.ofTransition`,
`BHW.BHWJostOrientedSourceNormalFormGeometryPatch.exists_source_realization`,
`BHW.BHWJostOrientedSourceNormalFormGeometryPatch.exists_source_realization_mem_U`,
`BHW.BHWJostOrientedTransitionData.orientedPatch_connected`,
`BHW.BHWJostOrientedSourceNormalFormGeometryPatch.orientedDomain_connected`,
`BHW.BHWJostOrientedClosedContinuationLoop.closing_orientedPatch_connected`,
`BHW.BHWJostOrientedClosedContinuationLoop.exists_initial_final_source_realizations_of_closing`,
`BHW.BHWJostOrientedClosedContinuationLoop.exists_initial_final_source_realizations_branch_eqs_of_closing`,
`BHW.BHWJostOrientedBranchFreeTransferNeighborhood.ofSourceNormalFormPatch`,
`BHW.BHWJostOrientedBranchFreeTransferNeighborhood.transfer_source_mem_next`,
`BHW.BHWJostOrientedBranchFreeTransferNeighborhood.transfer_target_mem_next`,
`BHW.BHWJostOrientedBranchFreeTransferNeighborhood.transfer_branch_agree_at_source`,
`BHW.BHWJostOrientedTransferControlHasUniqueNext`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.base`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.snoc`,
`BHW.BHWJostOrientedTransferContinuationTrace`,
`BHW.BHWJostOrientedTransferContinuationTrace.base`,
`BHW.BHWJostOrientedTransferContinuationTrace.snocAtTerminalNode`,
`BHW.BHWJostOrientedTransferContinuationTrace.exists_of_nodeTransferSteps`,
`BHW.BHWJostOrientedTransferContinuationTrace.ofNodeTransferSteps`,
`BHW.BHWJostOrientedTransferContinuationTrace.exists_of_subdivision`,
`BHW.BHWJostOrientedTransferContinuationTrace.ofSubdivision`,
`BHW.BHWJostOrientedTransferContinuationTrace.exists_of_transferCover`,
`BHW.BHWJostOrientedTransferContinuationTrace.ofTransferCover`,
`BHW.BHWJostOrientedTransferContinuationTrace.HasUniqueSteps`,
`BHW.BHWJostOrientedTransferContinuationTrace.hasUniqueSteps_base`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.base`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.snocAtTerminalNode`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.exists_of_nodeTransferSteps`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.ofNodeTransferSteps`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.exists_of_subdivision`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.ofSubdivision`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.exists_of_transferCover`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.ofTransferCover`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.toTerminalPointTrace`,
`BHW.BHWJostOrientedCertifiedTransferContinuationTrace.atEndpoint`,
`BHW.BHWJostOrientedCertifiedTransferTerminalPointTrace`,
`BHW.BHWJostOrientedCertifiedTransferTerminalPointTrace.toTerminalPointTrace`,
`BHW.BHWJostOrientedCertifiedTransferTerminalPointTrace.ofTracePoint`,
`BHW.BHWJostOrientedCertifiedTransferTerminalPointTrace.atEndpoint`,
`BHW.BHWJostOrientedCertifiedTransferTerminalPointTrace.point_mem_terminalLocalChart`,
`BHW.BHWJostOrientedTransferTerminalPointTrace`,
`BHW.BHWJostOrientedTransferTerminalPointTrace.ofTracePoint`,
`BHW.BHWJostOrientedTransferTerminalPointTrace.atEndpoint`,
`BHW.BHWJostOrientedTransferTerminalPointTrace.point_mem_terminalLocalChart`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.exists_of_nodeSteps`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.ofNodeSteps`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.exists_of_subdivision`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.ofSubdivision`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.exists_of_transferCover`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.ofTransferCover`,
`BHW.BHWJostOrientedSourcePatchContinuationChain.chart_is_lorentz_step_of_localChart`,
`BHW.BHWJostOrientedMaxRankClosedLoopSeed.exists_initial_final_source_realizations`,
`BHW.BHWSourcePatchContinuationAtlas.glued`,
`BHW.BHWSourcePatchContinuationAtlas.glued_eq_branch_of_mem`,
`BHW.BHWSourcePatchContinuationAtlas.glued_differentiableOn`,
`BHW.BHWSourcePatchContinuationAtlas.glued_eq_B0_of_mem`,
`BHW.bhw_glue_sourcePatchContinuationAtlas`,
and
`BHW.BHWJostOrientedMaxRankClosedLoopSeed.terminal_branch_eq_B0_on_seedRealizedClosingPatch`.
`BHW.BHWJostOrientedSourcePatchContinuationChain.localChart_consecutive_agree`
now derives chart agreement from the stored chain-level branch equality and
`branch_eq_local`; the earlier field `transition_patch_eq_sourcePatch` has
been removed as redundant.  The closing oriented-patch representative helpers
now expose the initial/terminal source representatives, plus the
`branch_eq_orientedPullback` rewrites, for every invariant in
`L.closing_orientedPatch`; the remaining terminal-seed producer can therefore
focus on the genuine closed-path source-branch equality.  This introduces no
new `sorry` and does not prove
the hard Hall-Wightman/Jost closed-loop seed theorem; that seed remains the
next genuine mathematical blocker after the local descent producers are in
place.

The producer-level assembly has been split into
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedContinuationProducers.lean`.
It checks
`BHW.bhw_jost_orientedBranchFreeTransferNeighborhood_at_of_sourceNormalFormProducer`,
which builds branch-free transfer neighborhoods from a normal-form patch
producer plus uniform descent, and
`BHW.bhw_jost_orientedContinuationChain_of_transferCover`, the top-level
spelling of the compact transfer-cover chain fold.  It also provides
`BHW.bhw_jost_orientedContinuationChainAt_of_pathConnected_transferCover`,
which chooses a path from the fixed base point to each point of a
path-connected `U` and folds the corresponding transfer cover into a selected
terminal chain.  The provenance-retaining analogues are now also checked:
`BHW.bhw_jost_orientedTransferContinuationTrace_of_transferCover` and
`BHW.bhw_jost_orientedTransferContinuationTraceAt_of_pathConnected_transferCover`
select transfer traces from the same compact-cover data.  The certified
analogues
`BHW.bhw_jost_orientedCertifiedTransferContinuationTrace_of_transferCover` and
`BHW.bhw_jost_orientedCertifiedTransferContinuationTraceAt_of_pathConnected_transferCover`
select traces with stored `HasUniqueSteps` certificates when each
center-forgotten transfer control has the one-step uniqueness theorem.  The final mechanical
producer
`BHW.bhw_jost_orientedGluedBranch_of_pathConnected_transferCover` takes those
trace selections, a terminal-point trace comparison theorem, and the initial
chart, and returns the glued holomorphic source-patch branch on `U`.  It also
provides
`BHW.BHWOrientedContinuationChainAtlasData`,
`BHW.BHWOrientedContinuationChainAtlasData.to_sourcePatchContinuationAtlas`,
`BHW.BHWOrientedContinuationChainAtlasData.exists_glued_branch`,
`BHW.BHWOrientedContinuationChainAtlasData.ofSameEndpointComparisons`,
`BHW.BHWOrientedContinuationChainAtlasData.terminal_base_agree_of_sameEndpointComparison`,
`BHW.BHWOrientedContinuationChainAtlasData.ofSameEndpointComparisonsAndBaseChain`,
`BHW.BHWOrientedContinuationChainAtlasData.ofSameEndpointComparisonsAndInitialChart`,
`BHW.BHWOrientedContinuationTraceAtlasData`,
`BHW.BHWOrientedContinuationTraceAtlasData.chainAt`,
`BHW.BHWOrientedContinuationTraceAtlasData.to_chainAtlasData`,
`BHW.BHWOrientedContinuationTraceAtlasData.to_sourcePatchContinuationAtlas`,
`BHW.BHWOrientedContinuationTraceAtlasData.exists_glued_branch`,
`BHW.BHWOrientedContinuationTraceAtlasData.ofSelectedComparisonsAndInitialChart`,
`BHW.BHWOrientedContinuationTraceAtlasData.ofTerminalPointComparisonsAndInitialChart`,
`BHW.BHWOrientedContinuationTraceAtlasData.ofCertifiedTerminalPointComparisonsAndInitialChart`,
`BHW.BHWOrientedContinuationTraceAtlasData.ofPathConnectedTransferCoverAndInitialChart`,
`BHW.bhw_jost_orientedGluedBranch_of_certifiedTraces`,
`BHW.bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover`,
`BHW.bhw_jost_orientedGluedBranch_of_pathConnected_sourceNormalFormProducer`,
`BHW.bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover_retargetedComparisons`,
`BHW.bhw_jost_orientedGluedBranch_of_pathConnected_sourceNormalFormProducer_retargetedComparisons`,
`BHW.BHWOrientedTerminalChainComparisonData`, and
`BHW.BHWOrientedTerminalChainComparisonData.ofLocalChartComparison`,
`BHW.BHWOrientedTerminalChainComparisonData.ofRetargetedTerminalPointTraceComparison`,
`BHW.BHWOrientedTerminalChainComparisonData.ofCertifiedRetargetedTerminalPointTraceComparison`,
`BHW.BHWOrientedTerminalChainComparisonData.continuedValue_eq`, which
turn selected terminal chains plus same-endpoint comparison/base agreement
into the checked source-patch atlas and glued branch, turn selected transfer
traces plus terminal-point comparison into the checked source-patch atlas and
glued branch, and turn a produced terminal comparison patch into equality of
continued values.  The chain-atlas
constructor is not merely an endpoint wrapper: it retargets any terminal chart
containing an overlap point `y` to a chain ending at `y`, compares both
retargeted chains with the selected chain ending at `y`, and thereby proves
the full terminal-overlap `EqOn`.  The base-chain constructor similarly
retargets one normalized base chain to any `z ∈ Ω0 ∩ U` and uses
same-endpoint comparison to derive the atlas base agreement field.  The
trace-atlas constructor avoids the arbitrary-chain comparison surface
altogether: it observes selected transfer traces at the overlap point, applies
terminal-point trace comparison, rewrites by `branch_eq_local`, and proves
base agreement by comparing against the zero-step base trace observed inside
the initial chart.  The certified-trace variant strengthens the strict route
surface by requiring each selected trace to carry
`HasUniqueSteps`; the terminal comparison theorem then consumes certified
terminal-point traces, not raw observations.  This keeps the carrier/API file
below the hard-frontier size limit and introduces no new analytic assumption.
The monodromy-facing certified variants now take comparison of the two
terminal-retargeted certified chains as the hard input; the conversion from
that chain comparison to `BHWLocalChartTerminalComparisonData` for the two
original terminal local charts is checked by the two retargeted-comparison
constructors above.  Thus the future closed-path theorem can target the
natural same-endpoint chain object and does not also need to prove the atlas
local-chart packaging.

The finite one-step propagation layer is now split into
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedContinuationUniqueness.lean`.
It checks
`BHW.bhw_jost_orientedTerminalComparison_of_sharedTransferSkeleton`, a
noncomputable data constructor which takes a fixed finite node list, the same
center-forgotten transfer control at each adjacent step, one-step uniqueness
for every stored control, two chart sequences produced by those same transfer
calls, and initial branch equality on a source seed.  It then inductively
feeds the terminal comparison patch from step `j` as the source seed for step
`j+1`, applies `BHWJostOrientedTransferControlHasUniqueNext`, rewrites the
produced transfer charts by the stored `step_chart_A/B` equations, and returns
`BHWLocalChartTerminalComparisonData` at the final node.  This closes the
former prose-only finite uniqueness induction for shared skeletons; it still
does not compare different selected paths or prove closed-path monodromy.

The closed-loop packaging bridge is now split into
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedContinuationMonodromyComparison.lean`.
It checks
`BHW.BHWJostOrientedClosedContinuationLoop.normalizedBaseChain`,
`BHW.BHWJostOrientedClosedContinuationLoop.terminalChainComparison_base_of_sourceMonodromy`,
and
`BHW.BHWJostOrientedClosedContinuationLoop.terminalChainComparison_base_of_closingPatchTerminalSeedData`.
These constructors take a closed loop whose source monodromy has already been
proved on the stored closing patch and package it as
`BHWOrientedTerminalChainComparisonData` between the loop chain and the
normalized zero-step base chain built from the initial chart.  This is pure
bookkeeping: `closing_patch_sub_final` gives the terminal-chart side,
`closing_patch_sub_start` plus `start_patch_sub` gives the base-chart side,
and `start_agree` rewrites the base branch to `B0`.

The open-chart BHW near-identity input is now checked in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedBHWInvariance.lean`.
It provides `BHW.complexLorentz_exp_nhd_of_one`,
`BHW.reMatrixCLie`, `BHW.imMatrixCLie`,
`BHW.matrix_re_im_decomp_CLie`, `BHW.exp_map_ofReal_bridge`,
`BHW.bhw_near_identity_invariance_on_open`, and
`BHW.bhw_local_complexLorentz_invariance_of_real_invariance`, and
`BHW.bhw_branch_constant_along_complexLorentz_path`, plus the chart-specialized
`BHW.BHWJostLocalOrientedContinuationChart.branch_constant_along_complexLorentz_path`
and the closed-loop seed data constructor
`BHW.BHWJostOrientedMaxRankClosedLoopSeed.of_sourceRealized_branch_eq`,
the finite-chain telescope
`BHW.BHWJostOrientedSourcePatchContinuationChain.terminal_Psi_eq_initial_Psi_of_mem_all_orientedTransitions`,
the propagated-seed step
`BHW.BHWJostOrientedTransitionData.propagate_eqOn_to_right_maxRank`,
the generic target-seed propagation theorem
`BHW.exists_maxRankSeed_eqOn_of_connected_domain`,
the seed-producing propagated step
   `BHW.BHWJostOrientedTransitionData.exists_propagatedSeed_to_right`,
   and the common-transition-seed constructor
   `BHW.BHWJostOrientedMaxRankClosedLoopSeed.of_commonTransitionSeed`, and the
   closing-domain package theorem
   `BHW.BHWJostOrientedMaxRankClosedLoopSeed.exists_of_connectedDomainPropagation`.
The terminal finite-overlap data interface is checked in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedBHWFiniteOverlap.lean`;
it provides
`BHW.sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_local_basis`,
`BHW.sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected`,
`BHW.sourceOrientedMaxRank_local_connectedMaxRank_basis_fullFrame`,
`BHW.sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_exceptionalLocalBasis`,
`BHW.sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_rankDeficientMaxRankLocalImageProducer`,
`BHW.BHWJostOrientedFiniteOverlapPropagationData`,
`BHW.BHWJostOrientedFiniteOverlapPropagationData.to_closedLoopSeed`,
`BHW.BHWJostOrientedFiniteOverlapPropagationData.to_orientedMonodromy`,
`BHW.BHWJostOrientedFiniteOverlapPropagationData.to_sourceMonodromy`,
`BHW.BHWJostOrientedFiniteOverlapPropagationData.to_orientedMonodromy_headSliceIFT`,
`BHW.BHWJostOrientedFiniteOverlapPropagationData.to_sourceMonodromy_headSliceIFT`,
`BHW.BHWJostOrientedFiniteOverlapPropagationData.of_terminalSeedOnClosingPatch_headSliceIFT`,
`BHW.BHWJostOrientedFiniteOverlapPropagationData.sourceMonodromy_of_terminalSeedOnClosingPatch_headSliceIFT`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData.of_sourceRealized_branch_eq`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData.of_sourcePatch_eqOn`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData.of_closingPatch_sourceBranch_eq`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData.of_closingPatch_exists_sourceBranch_eq`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData.to_finiteOverlapPropagationData`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData.to_closedLoopSeed`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData.to_orientedMonodromy_headSliceIFT`,
`BHW.BHWJostOrientedClosingPatchTerminalSeedData.to_sourceMonodromy_headSliceIFT`,
`BHW.bhw_jost_closedChain_sourceMonodromy_of_closingPatchTerminalSeedData`,
`BHW.bhw_jost_closedChain_sourceMonodromy_of_closingPatch_exists_sourceBranch_eq`,
and
`BHW.exists_preconnectedRelOpen_maxRankSeed_inside`, plus
`BHW.BHWJostOrientedSourcePatchContinuationChain.exists_terminalSeed_of_finiteOverlapDomains`,
which iterates the checked one-step propagation theorem across an ordered
finite-overlap family of connected max-rank domains.  The same file also checks
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData`,
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.to_finiteOverlapPropagationData`,
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.to_closedLoopSeed`,
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.to_orientedMonodromy`,
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.to_sourceMonodromy`,
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.to_orientedMonodromy_headSliceIFT`,
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.to_sourceMonodromy_headSliceIFT`,
and
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_positiveDomains`
and `BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_zeroTransitions`,
with source-normal-form-friendly variants
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_positivePreconnectedDomains_headSliceIFT`
and
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_zeroTransitions_closedLoop_headSliceIFT`,
and the zero/positive split wrapper
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_preconnectedDomains_headSliceIFT`.
The same checked file now exposes the producer-facing package
`BHW.BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData`, with
mechanical consumers
`BHW.BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.to_finiteOverlapDomainData`,
`BHW.BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.to_finiteOverlapPropagationData`,
`BHW.BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.to_closedLoopSeed`,
`BHW.BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.to_orientedMonodromy_headSliceIFT`,
and
`BHW.BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.to_sourceMonodromy_headSliceIFT`,
plus the public endpoint
`BHW.bhw_jost_closedChain_sourceMonodromy_of_preconnectedFiniteOverlapData`,
and the zero-transition endpoints
`BHW.BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.exists_of_zeroTransitions`
and `BHW.bhw_jost_closedChain_sourceMonodromy_of_zeroTransitions`.
   This closes the
   previous-branch-as-seed gap for local proper-complex invariance: an already
constructed holomorphic branch on an open source carrier can now be used as
the starting branch for the next Hall-Wightman descent, provided it has the
stored real restricted-Lorentz invariance on that carrier; the path theorem
then propagates this equality along any proper-complex Lorentz path whose
source orbit remains in the carrier, and the chart-specialized theorem feeds
the required real-invariance hypothesis directly from the stored chart fields.
The seed constructor then packages a genuinely produced terminal/initial
source-realized branch equality on a nonempty relatively open max-rank seed
into the exact `BHWJostOrientedMaxRankClosedLoopSeed` object consumed by the
identity-principle layer.  This removes the remaining constructor bookkeeping;
the common-transition constructor separately handles the purely finite
telescope case where the same seed is carried by every oriented transition
patch of the closed chain.  The remaining finite-overlap Hall-Wightman/Jost
work now has a checked one-step identity-propagation bridge: an accumulated
oriented germ equality on a nonempty max-rank seed propagates across one
oriented transition to the max-rank part of the next transition patch whenever
the intermediate domain has connected max-rank part, and the chart layer now
extracts a new nonempty preconnected relatively open max-rank seed inside that
   transition patch.  The checked finite-overlap induction theorem now
   performs that iteration once the Hall-Wightman geometry has supplied the
   ordered relatively open nonempty preconnected domains and adjacency
   containments.  The new max-rank
   assembly theorem separates a reusable topology step: to prove
   `D ∩ MaxRank` connected it is enough to prove `D` connected, use the
   checked hard-range density of `MaxRank` in every relatively open oriented
   patch, and supply arbitrarily small relatively open neighborhoods whose
   max-rank parts are connected.  The max-rank-center half of that local basis
   is now also checked by the full-frame chart shrinker; the remaining local
   basis input is precisely the exceptional-rank source-oriented local-image
   case.  The old connected local-image packet is not strong enough here:
   it proves connectedness of the whole local image, while finite-overlap
   propagation consumes connectedness after intersecting with the max-rank
   stratum.  The checked interface
   `BHW.SourceOrientedRankDeficientMaxRankLocalImageData` and extraction theorem
   `BHW.sourceOrientedRankDeficientConnectedMaxRankPatchAt_of_localImageProducer`
   now isolate the exact remaining Schur/residual obligation.  The helper
   `BHW.isConnected_image_inter_sourceOrientedMaxRank_of_connected_preimage`
   reduces the final connectedness field to the finite-dimensional parameter
   statement
   `IsConnected (parameterBox ∩ {p | SourceOrientedMaxRankAt d n (image p)})`;
   the set equality between this preimage image and `image '' parameterBox ∩
   MaxRank` is checked separately as
   `BHW.image_inter_preimage_sourceOrientedMaxRank_eq`.  The checked adapter
   `BHW.SourceOrientedRankDeficientVarietyLocalImageData.to_maxRankLocalImageData_of_connected_preimage`
   upgrades the older connected local-image packet to the strengthened packet
   once this preimage connectedness is supplied.  Thus the remaining geometric
   work is the exceptional local max-rank-basis production plus the
   source-backed finite-overlap domains themselves.  The subtype-to-ambient
   adapter
   `BHW.SourceOrientedRankDeficientVarietyLocalImageData.ofSubtype` is also
   checked: a concrete producer may work internally with an
   `imageV : P -> BHW.SourceOrientedVariety d n`, prove `imageV '' P` open in
   the subtype and contained in the requested ambient neighborhood, and then
   expose the existing ambient packet by composing with `Subtype.val`.  The
   strengthened constructor
   `BHW.SourceOrientedRankDeficientMaxRankLocalImageData.ofSubtype` is checked
   as well: after the Schur connectedness theorem proves the max-rank
   preimage connected in parameter space, it directly returns the finite-overlap
   packet.
   The remaining work is to produce the terminal closing domain and assemble
   the resulting terminal
   seed into `BHWJostOrientedFiniteOverlapPropagationData`; once that data is
   available, `to_closedLoopSeed` feeds it into the checked closing-domain seed
   package, and `to_sourceMonodromy_headSliceIFT` feeds it directly into the
   checked source-monodromy endpoint.  This introduces no new `sorry`.

The rank bridge file
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedRankBridge.lean`
checks the finite-dimensional rank conversions needed by the next local-chart
dispatch: `BHW.sourceGramMatrixRank_le_spacetime_source_min`,
`BHW.sourceOriented_notMaxRank_sourceGramMatrixRank_lt_min`,
`BHW.sourceOriented_notMaxRank_sourceGramMatrixRank_lt_fullFrame`,
`BHW.sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt`,
`BHW.sourceOrientedExceptionalRank_invariant_iff_hwSourceGramExceptionalRankAt`,
the corresponding transport lemmas under equality of oriented invariants, and
the fact that oriented max/exceptional rank depends only on the ordinary Gram
coordinate.  The rank-deficient strict inequalities are proved from the
spacetime/source minimum upper bound plus failure of the equality defining
`SourceOrientedMaxRankAt`.  The upper bound is proved from
`sourceGramMatrixRank_eq_restrictedMinkowskiRank_range`,
`finrank_range_sourceCoefficientEval_le`, and `Submodule.finrank_le`.
The companion file
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedLowRankDeterminants.lean`
now checks the arity/rank and determinant consequences used by the normal-form
route: `BHW.sourceGramMatrixRank_le_arity` gives the selected rank bound
`r ≤ n`, and `BHW.sourceFullFrameDet_eq_zero_of_sourceRank_lt` proves that every full-frame
determinant coordinate vanishes below source Gram rank `d + 1`, using the
selected full-frame Gram determinant identity and the checked nonzero-minor
rank bound.  It also checks
`BHW.sourceOrientedMinkowskiInvariant_eq_of_sameGram_rank_lt`, so in the
strict low-rank branch ordinary Gram equality already gives equality of the
full oriented invariant.

The no-tube rank-deficient algebraic normal-form proof now has a checked
adapted-representative gate in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedAdaptedRepresentative.lean`.
It may not call `hwLemma3_normalFormTransportData` on an arbitrary realization
of a source-oriented variety point, because radical tail vectors can make
`finrank (range sourceCoefficientEval)` strictly larger than the ordinary Gram
rank.  The checked finite-dimensional theorem
`BHW.sourceComplexGramVariety_exists_adaptedSourceRepresentative` says that
for any ordinary algebraic source Gram point, there is a same-Gram
representative whose source-vector span dimension is exactly
`sourceGramMatrixRank`.  Its proof is not an extended-tube argument; it uses
exact-rank symmetric dot-Gram factorization
(`exists_fullRank_sourceComplexDotGram_of_rankExact`), pads the rank
coordinates into `Fin (d+1)`, transports through
`complexMinkowskiToDotLinearEquiv.symm`, proves
`sourceComplexDotGram_padded_eq`, and compares the coefficient span with the
padded coordinate subspace via
`finrank_sourceCoefficientEval_range_le_of_paddedDot` and
`sourceGramMatrixRank_le_finrank_sourceCoefficientEval_range`.  The checked
oriented low-rank theorem
`BHW.sourceOriented_lowRank_exists_adaptedRepresentative` then combines this
with `sourceOrientedMinkowskiInvariant_eq_of_sameGram_rank_lt`, so the adapted
representative realizes the original full oriented invariant.  This replaces
the false shortcut
`sourceCoefficientEval_finrank_range_eq_sourceGramRank`, which must not be
introduced as a theorem.

Latest local connected-basis refinement, 2026-05-05: the rank-deficient
no-tube local-image branch uses the checked one-way shifted-tail realization
for Schur image-surjectivity.  The proof docs no longer require a same-radius
compatible-box theorem at the tail layer:
`sourceShiftedTailSmallRealization` supplies the small residual tail tuple
after the finite diagonal normalization from the ambient shifted metric to the
Euclidean tail model, and the forward containment of the chosen
head-gauge/mixed/tail parameter box is a separate continuity/polynomial-shrink
obligation stored in the residual-polydisc/local-image data.  This removes the
old theorem-shape gap without imposing an artificial bidirectional estimate on
the quadratic tail invariant map in the local
`sourceOrientedGramVariety_local_connectedRelOpen_basis` transcript; the
remaining local-image producer obligations are now explicit shifted-tail
normalization, determinant recovery, and rank-slice connectedness theorems.
Its Lean implementation has now started at the lower support layer: the checked
files `SourceOrientedConnected.lean`, `SourceOrientedLocalBasis.lean`, and
`SourceOrientedRankDeficientLocalImage.lean` prove the connected-component
topology, the max-rank/rank-deficient stratum dispatcher, and the topological
extraction from an abstract rank-deficient local-image packet.  The same
local-image file now also contains the strengthened max-rank-connected packet:
the Schur/residual producer must instantiate the finite head/mixed/tail
parameter box and prove both relative openness of the image and
`IsConnected (image '' parameterBox ∩ MaxRank)`.  The extraction theorem first
shrinks an arbitrary relatively open target `U` to an ambient open slice and
then returns exactly the exceptional input consumed by
`sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_exceptionalLocalBasis`.
The connectedness proof should use the checked image-transport helper: define
the max-rank preimage inside the parameter box, rewrite it by the Schur rank
formula to a product of the head/mixed box with the symmetric rank-exact
residual cone, prove that product connected, and apply
`isConnected_image_inter_sourceOrientedMaxRank_of_connected_preimage`.
The remaining concrete lemma is
`BHW.sourceOriented_rankDeficient_parameterMaxRank_connected` in the hard range
`d + 1 <= n`: after expanding the normal-form map, ordinary rank is invariant
under the stored oriented transport and the Schur complement gives
`rank(full Gram) = N.r + rank(residual tail Gram)`, so maximal rank is exactly
the residual exact-rank condition `rank = (d + 1) - N.r`.  The proof is the
same product-connectedness pattern as the checked ordinary singular theorem
`sourceComplexGramVariety_local_rankExact_connected_basis_singular`, using the
connected symmetric head ball, connected mixed ball, and
`matrixSymmetricRankExactCone_small_connected` for the residual tail.  The
hard-range rewrite from oriented max-rank to ordinary full-frame rank is now
checked as
`BHW.sourceOrientedMaxRankAt_iff_sourceGramMatrixRank_eq_fullFrame`, with the
actual-source specialization
`BHW.sourceOrientedMaxRankAt_invariant_iff_sourceGramMatrixRank_eq_fullFrame`.
The oriented parameter proof should call the first theorem after rewriting
`(toInv c).gram`; it should call the second only when the normal parameter map
is still expressed as an actual source vector.  The parameter-side product
step is now checked separately as
`BHW.isConnected_sourcePrincipalSchur_rankExact_parameterSet`; the oriented
proof should use it before transporting by the normal-parameter coordinate
equivalence via the checked helper
`BHW.isConnected_preimage_homeomorph` for the checked normal-parameter
homeomorphism.  The older continuous-linear helper
`BHW.isConnected_preimage_continuousLinearEquiv` remains valid for genuinely
linear chart coordinates, but it is not the normal-parameter route.
The pure principal-Schur oriented max-rank slice is now checked in
`SourceOrientedSchurParameter.lean`:
`BHW.sourcePrincipalSchur_orientedMaxRank_parameterSet_eq` rewrites the
max-rank parameter predicate to residual exact rank, and
`BHW.isConnected_sourcePrincipalSchur_orientedMaxRank_parameterSet` packages
the resulting product connectedness.  The ambient inverse-transport variants
`BHW.isConnected_sourcePrincipalSchur_transported_orientedMaxRank_parameterSet`
and
`BHW.isConnected_sourcePrincipalSchur_transported_orientedMaxRank_preimage_of_eq`
are checked for transports that really are homeomorphisms of the full
oriented invariant coordinate space.  For source changes, the route now uses
the checked variety-relative analogues
`BHW.isConnected_sourcePrincipalSchur_varietyTransported_orientedMaxRank_parameterSet`
and
`BHW.isConnected_sourcePrincipalSchur_varietyTransported_orientedMaxRank_preimage_of_eq`:
the normal Schur parameter is supplied as a
`BHW.SourceOrientedVariety d n` point, it is identified on the parameter box
with `(sourcePrincipalSchurGraph ..., δ p)`, and the max-rank slice is then
definitionally the same connected product slice by
`BHW.SourceOrientedVarietyTransportEquiv.invFun_maxRank_iff`.  Consequently
the remaining oriented normal-form proof only has to identify the checked
normal subtype-valued parameter map with the principal Schur graph on the
parameter box, prove that the concrete image agrees with
`(N.originalNormalVarietyPoint p).1`, and then move connectedness through the
checked normal-parameter coordinate homeomorphism.
There is no additional two-sheet obstruction from the determinant coordinates:
`SourceOrientedMaxRankAt` is defined only from `G.gram`, and the determinant
coordinates are continuous functions of the same source-vector parameters on
this local image.  The exact Lean proof should therefore:

1. define
   `parameterMaxRank = P ∩ {c | SourceOrientedMaxRankAt d n (toInv c)}`;
2. rewrite the predicate through `toInv` with
   `SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint_maxRank_iff_tail_rank`;
3. identify the normal parameter coordinates with a subtype-valued principal
   Schur point of `BHW.SourceOrientedVariety d n` and use
   `isConnected_sourcePrincipalSchur_varietyTransported_orientedMaxRank_preimage_of_eq`
   to identify this set with the product of the head ball, mixed ball, and
   `C ∩ {S | Sᵀ = S ∧ S.rank = (d + 1) - N.r}`;
4. invoke `isConnected_symmetric_matrix_ball`, `isConnected_matrix_ball`, and
   `matrixSymmetricRankExactCone_small_connected`, combine them with the
   transported checked Schur theorem above, and use the checked single
   finite-function coordinate model
   `sourceOrientedNormalParameterFiniteCoordHomeomorph` plus the pullback ball
   theorem `sourceOrientedNormalParameterBall_open_connected_center` for the
   small parameter ball.  Shrinking into the invertible-head locus is now the
   checked theorem
   `exists_sourceOrientedNormalParameterBall_subset_head_det_isUnit`.
The remaining implementation targets are the concrete exceptional
Schur/residual max-rank-connected local-image producer, now using
`BHW.SourceOrientedVarietyTransportEquiv` for source changes, and the
source-backed finite-overlap domains; Lean work should still not start at the
public adjacent seed or scalar-representative wrappers.

The transported neighborhood shrink for the exceptional normal image is now
checked as
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.exists_normalParameterBall_image_subset_open_and_head`.
Given an ambient open set `N0` containing the original exceptional point, it
chooses a positive-radius normal-parameter ball that is open, connected,
contains the center, lies in the invertible-head locus, and whose transported
normal-variety image lies in `N0 ∩ sourceOrientedGramVariety d n`.  This
removes another informal shrink from
`sourceOriented_rankDeficient_algebraicParameterBall`; the remaining hard
surjectivity step is Schur extraction and tail realization on the shrunken
normal neighborhood.

The normal Schur-coordinate continuity layer is also checked:
`BHW.continuous_sourceTailEmbed_apply`,
`BHW.continuous_sourceShiftedTailGram`,
`BHW.continuous_sourceOrientedNormalParameterSchurHead`,
`BHW.continuous_sourceOrientedNormalParameterSchurMixed`, and
`BHW.continuous_sourceOrientedNormalParameterSchurTail`.  These are the named
finite-coordinate continuity facts used by the estimate/shrink proof for the
head, mixed, and residual-tail Schur coordinates.

The first topology-only Schur shrink is now checked in
`SourceOrientedRankDeficientSchurShrink.lean`.  It adds the center identities
`BHW.sourceOrientedNormalParameterSchurHead_center`,
`BHW.sourceOrientedNormalParameterSchurMixed_center`, and
`BHW.sourceOrientedNormalParameterSchurTail_center`, plus
`BHW.exists_sourceOrientedNormalParameterBall_subset_schur_nhds`,
`BHW.exists_sourceOrientedNormalParameterBall_subset_coordinate_nhds`, and
`BHW.exists_sourceOrientedNormalParameterBall_subset_coordinate_bounds`.
Production Lean should use these theorems, together with
`BHW.sourceOrientedNormalParameterBall`, rather than reintroducing the retired
continuous-linear coordinate-box pseudocode.  The theorems say that arbitrary
neighborhoods of the center Schur head, mixed, and residual-tail coordinates,
and arbitrary positive raw head/mixed/tail coordinate radii, pull back to a
positive connected normal-parameter ball.

The combined normal-ball shrink is now checked in
`SourceOrientedRankDeficientNormalShrink.lean`, with ball monotonicity
`BHW.sourceOrientedNormalParameterBall_mono` in
`SourceOrientedNormalParameterBall.lean`.  The theorem
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.exists_normalParameterBall_image_subset_open_head_schur_and_coordinate_bounds`
chooses one positive normal-parameter ball satisfying all current topological
shrink requirements at once: open/connected/center, invertible head, image
inside an ambient open set and the source variety, Schur-coordinate
neighborhood constraints, and raw coordinate radius bounds.  The remaining
unproved part of the finite estimate theorem is therefore not topology but the
choice of the Schur neighborhoods/radii from the head gauge and shifted-tail
realization estimates.

The head-gauge-aware version of this common shrink is also checked as
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.exists_normalParameterBall_image_subset_open_headGauge_schur_and_coordinate_bounds`.
It first converts the symmetric-subtype gauge shrink into an ordinary
full-matrix Schur-head neighborhood, then chooses one normal-parameter ball
where the Schur head lies in `Head.U`, the local factor is entrywise close to
`1`, the mixed/tail Schur neighborhoods hold, and the raw head/mixed/tail
coordinate bounds hold.  Thus the finite estimate proof no longer has to
manually reconcile subtype neighborhoods with the ordinary matrix
neighborhoods consumed by the normal-Schur continuity lemmas.

The tail-window version of the same shrink is now checked as
`BHW.exists_sourceOrientedNormalParameterBall_subset_schurParameterWindow`
and
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.exists_normalParameterBall_image_subset_open_headGauge_schurParameterWindow`.
It shrinks the normal ball once more so the parameter ball is contained in the
full target-shaped Schur parameter window, while preserving the ambient-image,
invertible-head, head-gauge, and Schur-coordinate controls above.  This is the
checked bridge from the connected window theorem to the finite ball used by
the rank-deficient local-image producer.

The converse shrink needed by the strengthened local-image packet is now
checked as
`BHW.sourceOrientedRankDeficientSchurParameterWindow_subset_normalParameterBall`
and
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.exists_schurParameterWindow_image_subset_open_head_tailRank_connected`.
The first theorem is the finite-coordinate estimate: if the raw Schur head,
mixed, and tail radii are bounded by a positive normal-ball radius `epsilon`,
then the whole target-shaped Schur parameter window lies in that normal ball.
The second theorem applies the ambient normal-ball shrink, chooses one radius
`rho = epsilon / 2`, builds the tail-window choice at `rho`, and returns a
single Schur parameter window that is open, connected, centered, contained in
the invertible-head locus, whose transported original image lies in
`N0 ∩ sourceOrientedGramVariety`, and whose residual-tail exact-rank slice is
connected in the hard range `d + 1 <= n`.  This corrects the earlier possible
parameter-set mismatch: the producer will no longer combine connectedness of a
large Schur window with ambient containment of a smaller normal ball.  The same
Schur window now supplies all topology and shrink fields.
The checked assembly
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.maxRankLocalImageData_of_schurWindowCanonicalImage`
consumes a canonical-image theorem and returns the strengthened local-image
packet.  Its only extra hypothesis is: for the chosen Schur window, there is
an open subtype normal image `Omega` such that
`Omega ⊆ sourceOrientedNormalParameterVarietyPoint '' parameterBox` and
`sourceOrientedNormalParameterVarietyPoint parameterBox ⊆ Omega`.  The
head-gauge version below now supplies this canonical-image theorem.  All
shrink, transported containment, invertible-head, center, continuity,
max-rank/tail-rank rewrite, and residual exact-rank connectedness fields are
assembled.

Head-gauge correction, 2026-05-05: the canonical-image proof cannot use only
`Head.factor_gram`.  For a normal parameter `p`, the forward residual-tail
smallness available from the Schur window is stated for `p.head`; the
Schur-extraction inverse uses the gauge-selected factor of the head Gram
block.  Therefore the head-gauge data must remember a near-identity factor
domain and the left-inverse law
`Head.factor (sourceHeadFactorGramSymmCoord d r hrD H) = H` on that domain.
This makes the forward normal-image inclusion honest: after shrinking the
Schur head window into the factor domain, the gauge factor of the normal image
is definitionally the stored normal head, so
`sourceOrientedSchurResidualTailData_normalParameter_headGauge` reduces the
gauge-selected residual tail to the checked shifted-tail invariant.  The next
canonical-image transcript must therefore first produce a Schur window
contained in this factor domain, then prove the open extracted image
conditions.  A theorem that asserts openness of an arbitrary Schur-window image
without these head-gauge-domain controls is not Lean-ready.

Lean checkpoint for that correction: `SourceOrientedHeadGauge.lean` now
defines `sourceHeadFactorCoordinateWindow` and
`sourceHeadFactorGramSymmCoord`, and `SourceRankDeficientHeadGaugeData`
stores `factorDomain`, `factorDomain_coordinate`, `factorDomain_mem`, and
`factor_left_inverse`.  `SourceOrientedSchurTailNormal.lean` checks
`sourceOrientedSchurHeadBlockSymm_normalParameter`,
`sourceOrientedSchurResidualTailData_normalParameter_headGauge`, and its
membership form.  `SourceOrientedRankDeficientSchurWindowShrink.lean` checks
`exists_schurParameterWindow_image_subset_open_headDomain_tailRank_connected`
and the two `schurWindow_normalParameter_headGauge_residualTail_*` bridges.
It also checks
`SourceOrientedRankDeficientAlgebraicNormalFormData.maxRankLocalImageData_of_headGaugeSchurWindowCanonicalImage`,
the head-gauge-aware assembly wrapper that consumes a canonical-image theorem
with the head-domain containment as an explicit hypothesis.
The forward mixed-coordinate bridge is also checked as
`sourceSchurMixedCoeff_normalParameter_headGauge` and
`schurWindow_normalParameter_headGauge_mixedCoeff_eq`.
Thus the remaining canonical-image theorem may assume a window already shrunk
into the head-gauge factor domain; it no longer has to compare two different
head factors by hand.

Canonical extracted-image checkpoint, 2026-05-05, now closed:
`SourceOrientedRankDeficientCanonicalImage.lean` now defines the exact subtype
image candidate
`BHW.sourceOrientedHeadGaugeSchurExtractedImage`.  For a source-variety point
`Gv`, membership means: with
`Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn Gv.2`,
`H := Head.factor Acoord`, and
`T := sourceOrientedSchurResidualTailData d n r hrD hrn Gv.1 H`,
one has `Acoord ∈ Head.U`, `H` in the chosen head window, the extracted Schur
mixed coefficient in the chosen mixed window, and the gram/determinant
coordinates of `T` satisfy the tail eta bounds.  Two inclusions are now
checked:
`sourceOrientedNormalParameterVarietyPoint_mem_headGaugeSchurExtractedImage`
proves the forward image membership for every normal parameter in a
head-domain-compatible Schur window, using the checked head-gauge residual and
mixed extraction equalities; and
`sourceOrientedHeadGaugeSchurExtractedImage_subset_normalParameter_image`
proves the reverse inclusion in the hard source range by building the
head-gauge Schur residual packet, applying `Tail.tailRealize`, and calling
`sourceOriented_reconstruct_from_schurResidual`.  The file also checks
`isOpen_sourceOrientedHeadGaugeSchurExtractedImage` by finite-coordinate
continuity on the gauge unit patch, and packages the result as
`sourceOrientedHeadGaugeSchurWindowCanonicalImage`.

Checked openness transcript: the proof first establishes continuity of the
extracted coordinate maps on `SourceOrientedVariety d n`.
First, add `continuous_sourceOrientedSchurHeadBlock` on
`SourceOrientedGramData d n`, then the subtype-valued
`continuous_sourceOrientedSchurHeadBlockSymm_on_variety`.  The first proof is
finite-coordinate projection from `G.gram`; the second is `Continuous.subtype_mk`
after composing with `continuous_subtype_val`.  Next, for the head-gauge
factor condition, use `Head.factor_continuousOn` and `Head.U_open` to prove
that
`{Gv | Acoord Gv ∈ Head.U ∧ Head.factor (Acoord Gv) ∈ headWindow}` is open in
the subtype, by `ContinuousOn.isOpen_inter_preimage` after pulling back along
`Acoord`.  The mixed map
`Gv ↦ sourceSchurMixedCoeff n r hrn Gv.1 (sourceOrientedSchurHeadBlock n r hrn Gv.1)`
and the residual-tail gram/determinant maps are finite sums/products plus
matrix inverse on the unit-head patch; their continuity is needed only on the
open set where the head-gauge condition holds, and the head-gauge determinant
unit theorem supplies that unit patch.  Once these maps are continuous on that
open patch, intersect the preimages of
`sourceOrientedMixedCoordinateWindow n r mixedRadius`, the finitely many
strict gram eta balls, and the finitely many strict determinant eta balls.
This gives
`isOpen_sourceOrientedHeadGaugeSchurExtractedImage`, after which the full
canonical-image theorem is just the two checked inclusions above with
`Ω := sourceOrientedHeadGaugeSchurExtractedImage ...`.  Finally,
`SourceOrientedRankDeficientAlgebraicNormalFormData.maxRankLocalImageData_of_headGaugeSchurWindow`
feeds the canonical-image theorem into the checked Schur-window shrink and
transport adapters, but this last wrapper is only conditional on the legacy
full-matrix head-gauge interface.  A sanity check with Gemini on 2026-05-05
confirmed the mathematical issue: for `r >= 2`, `H ↦ H η Hᵀ` is not locally
injective on any full open matrix neighborhood of `1`, because of the local
complex orthogonal stabilizer.  Therefore the constructible route replaces
the full head window by a transverse slice.  The sliced parameter-window and
canonical-image packet are now checked:
`SourceOrientedRankDeficientSlicedNormalParameter`,
`sourceOrientedRankDeficientSlicedSchurParameterWindow`,
`sourceOrientedRankDeficientSlicedSchurParameterWindow_open_connected`,
`isConnected_sourceOrientedRankDeficientSlicedSchurParameterWindow_tailRank`,
`sourceOrientedHeadSliceGaugeSchurWindowCanonicalImage`, and
`SourceOrientedRankDeficientAlgebraicNormalFormData.maxRankLocalImageData_of_headSliceGaugeSchurWindow`
give the constructible local-image producer once a
`SourceRankDeficientHeadSliceGaugeData` chart is supplied.  The next
producer-level blocker is therefore the finite-dimensional inverse-function
construction of that sliced head-gauge chart at the canonical head metric.

The downstream transport adapter for that producer is now checked in
`SourceOrientedRankDeficientLocalImageTransport.lean`.  The theorems
`BHW.SourceOrientedRankDeficientVarietyLocalImageData.ofNormalImageTransport`
and
`BHW.SourceOrientedRankDeficientMaxRankLocalImageData.ofNormalImageTransport`
convert an open canonical normal image `Ω` into the old source-oriented
local-image packets by using the checked `SourceOrientedVarietyTransportEquiv`
inverse image, the exact normal-parameter image equality, and the stored
continuity/center facts for `N.originalNormalVarietyPoint`.  Thus the concrete
Schur/residual producer no longer has to reprove transported openness or
centeredness.  Its remaining inputs are exactly: a connected parameter window
containing the normal center, an open normal image `Ω`, the two-sided image
coverage between `Ω` and the parameter window, transported containment in the
requested ambient neighborhood, and, for the strengthened packet, connectedness
of the max-rank preimage inside the same window.
The follow-up variants
`BHW.SourceOrientedRankDeficientVarietyLocalImageData.ofNormalImageTransport_of_parameter_mem`
and
`BHW.SourceOrientedRankDeficientMaxRankLocalImageData.ofNormalImageTransport_of_parameter_mem`
derive the transported containment from pointwise membership of the parameter
image plus the same surjectivity onto `Ω`.  The remaining producer therefore
does **not** need a separate global proof that
`sourceOrientedVarietyUnderlyingSet (N.varietyTransport.invFun '' Ω)` lies in
`N0`; it only needs the normal-ball membership supplied by the shrink theorem
and the canonical Schur extraction/surjectivity proof.
For the strengthened max-rank packet, the checked adapter
`BHW.SourceOrientedRankDeficientMaxRankLocalImageData.ofNormalImageTransport_of_tailRank_connected`
now takes the connectedness hypothesis in the final residual-tail form:
`parameterBox ∩ {p | rank (sourceOrientedNormalParameterSchurTail p) =
d + 1 - N.r}`.  The producer no longer has to restate that as a transported
`SourceOrientedMaxRankAt` preimage.  On the corrected route the parameter box
is not the full head-matrix polydisc: its head coordinate is an open connected
neighborhood inside the slice source of `SourceRankDeficientHeadSliceGaugeData`.
This sliced transport has now been implemented directly through the abstract
`ofSubtype` adapter: the image map is
`N.varietyTransport.invFun ∘ sourceOrientedSlicedNormalParameterVarietyPoint`,
openness is the inverse image of the checked extracted image, and the max-rank
preimage is rewritten pointwise by
`originalNormalVarietyPoint_maxRank_iff_tail_rank` after forgetting the slice
proof on the head coordinate.

The head-gauge shrink layer is now checked in
`SourceOrientedHeadGaugeSupport.lean`:
`BHW.sourceRankDeficientHeadGauge_factor_continuousAt_center`,
`BHW.sourceRankDeficientHeadGauge_exists_factor_nhds`,
`BHW.sourceRankDeficientHeadGauge_exists_factor_coordinate_bound`.  These do
not assert existence of a head-gauge chart, and they are tied to the legacy
full-matrix data surface.  They remain useful only as conditional shrink
support until refactored to the slice domain.  The corrected source file now
adds `SourceHeadGaugeSlice`, `sourceHeadGaugeSliceCenter`,
`sourceHeadGaugeSliceCoordinateWindow`,
`isOpen_sourceHeadGaugeSliceCoordinateWindow`, and
`SourceRankDeficientHeadSliceGaugeData`.  `SourceOrientedSchurTailSliceNormal.lean`
now checks the first sliced algebraic consumers:
`sourceRankDeficientHeadSliceGauge_factor_det_unit_of_domain`,
`sourceOrientedSchurResidualTailData_normalParameter_headSliceGauge`,
`sourceSchurMixedCoeff_normalParameter_headSliceGauge`, and
`sourceOrientedSchurResidualTailData_normalParameter_headSliceGauge_mem_variety`.
These are the exact replacements for the old full-domain forward extraction
bridges: if a normal parameter's head matrix is the value of a slice point
inside the gauge domain, then Schur extraction recovers the stored mixed
coordinate and shifted residual tail.  The future head-gauge existence theorem
must construct the sliced data by the inverse-function theorem on the linear
slice `H * η = (H * η)ᵀ`, not a full-matrix local inverse.  The bridge
`BHW.sourceRankDeficientHeadGauge_exists_matrix_nhds_factor_coordinate_bound`
must likewise be replaced by a slice-to-matrix conversion for the sliced
parameter box.

The sliced reverse-image producer now has its Witt/head-normalizer membership
input checked.  The legacy normalizer has been factored through the minimal
head-factor interface `BHW.SourceRankDeficientHeadFactorData`, whose only
mathematical fields are the symmetric-head neighborhood, the chosen factor, the
signature-relative Gram identity, and determinant invertibility.  Both the
legacy full gauge and the corrected sliced gauge forget to this interface, so
the checked Witt proof no longer depends on `factorDomain`, coordinate-window,
or left-inverse fields.  The sliced public theorem surface is:

```lean
theorem BHW.sourceOrientedSchurResidualTailData_mem_variety_headSliceGauge
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : BHW.SourceRankDeficientHeadSliceGaugeData d r hrD)
    {G : BHW.SourceOrientedGramData d n}
    (hGvar : G ∈ BHW.sourceOrientedGramVariety d n)
    (hHead :
      BHW.sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    BHW.sourceOrientedSchurResidualTailData d n r hrD hrn G
        (Head.factor
          (BHW.sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)).1 ∈
      BHW.sourceShiftedTailOrientedVariety d r hrD (n - r)
```

Its proof is not a duplicate copy: `sourceOrientedSchurResidualTailData_mem_variety_headFactor`
runs the existing Witt/head-normalization argument against
`SourceRankDeficientHeadFactorData`, and
`sourceOrientedSchurResidualTailData_mem_variety_headSliceGauge` applies it to
`Head.toHeadFactorData`, where the factor is `(Head.factor A).1`.  The companion
constructor `sourceOriented_schurResidualData_of_headSliceGauge` is also
checked.  The extracted-image openness and reverse-inclusion half have also
been refactored through the same head-factor interface:
`sourceOrientedHeadSliceGaugeSchurExtractedImage`,
`isOpen_sourceOrientedHeadSliceGaugeSchurExtractedImage`, and
`sourceOrientedHeadSliceGaugeSchurExtractedImage_subset_normalParameter_image`
are checked.  The forward and reverse sliced parameter-window packet is now
also checked in `SourceOrientedRankDeficientSliceParameter.lean`,
`SourceOrientedRankDeficientSchurWindowShrink.lean`, and
`SourceOrientedRankDeficientCanonicalImage.lean`.  The old ambient-matrix head
window has been replaced by a genuine slice-head parameter space, its
coordinate window is path-connected by the straight segment inside the affine
slice, and the checked local-image wrapper consumes the sliced canonical-image
theorem.  The remaining local producer target is the inverse-function theorem
construction of `SourceRankDeficientHeadSliceGaugeData`.

Head-slice inverse-function readiness, 2026-05-06.  The finite-dimensional
coordinate reduction for that producer has now started in
`SourceOrientedHeadSliceGaugeIFT.lean`.  The checked coordinate is not the full
matrix variable `H`, but the symmetric submodule variable
`K = H * η - η`, where `η := sourceHeadMetric d r hrD`.  The file checks:

```lean
def BHW.sourceSymmetricMatrixSubmodule (r : ℕ) :
  Submodule ℂ (Matrix (Fin r) (Fin r) ℂ)

theorem BHW.sourceHeadMetric_mul_self
  (d r : ℕ) (hrD : r < d + 1) :
  sourceHeadMetric d r hrD * sourceHeadMetric d r hrD = 1

def BHW.sourceHeadGaugeSliceSymmCoordHomeomorph
  (d r : ℕ) (hrD : r < d + 1) :
  SourceHeadGaugeSlice d r hrD ≃ₜ sourceSymmetricMatrixSubmodule r

def BHW.sourceHeadSliceGramPolynomial
  (d r : ℕ) (hrD : r < d + 1) :
  sourceSymmetricMatrixSubmodule r → sourceSymmetricMatrixSubmodule r

theorem BHW.sourceHeadSliceGramPolynomial_eq_factorGram
  (d r : ℕ) (hrD : r < d + 1)
  (K : sourceSymmetricMatrixSubmodule r) :
  (sourceHeadSliceGramPolynomial d r hrD K :
      Matrix (Fin r) (Fin r) ℂ) =
    (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1 *
      sourceHeadMetric d r hrD *
      (sourceHeadGaugeSliceOfSymmCoord d r hrD K).1ᵀ

def BHW.sourceSymmetricMatrixCoordinateWindow
  (r : ℕ) (ρ : ℝ) :
  Set (sourceSymmetricMatrixSubmodule r)

theorem BHW.exists_sourceHeadGaugeSliceCoordinateWindow_subset_of_mem_nhds_center
  (d r : ℕ) (hrD : r < d + 1)
  {V : Set (SourceHeadGaugeSlice d r hrD)}
  (hV : V ∈ 𝓝 (sourceHeadGaugeSliceCenter d r hrD)) :
  ∃ ρ : ℝ, 0 < ρ ∧
    sourceHeadGaugeSliceCoordinateWindow d r hrD ρ ⊆ V
```

Mathematically, if `H` is in the slice and `K = Hη - η`, then
`H = (η + K)η` because `η² = 1`, and hence
`HηHᵀ = (η + K)η(η + K) = η + 2K + KηK`.  The derivative at the origin is
therefore the continuous linear equivalence `K ↦ 2K`, bundled as
`sourceHeadSliceGramPolynomialDerivEquiv`.

The local Lean producer for
`SourceRankDeficientHeadSliceGaugeData` is now checked:

1. Register the local matrix sup-norm instances for
   `Matrix (Fin r) (Fin r) ℂ`, use the checked finite-dimensional complete
   instance for the symmetric submodule, and prove
   `HasStrictFDerivAt (sourceHeadSliceGramPolynomial d r hrD)
   (sourceHeadSliceGramPolynomialDerivEquiv r : _ →L[ℂ] _) 0`.  This is now
   checked in Lean.  The implementation avoids changing to
   `Matrix.Norms.Operator`: it builds the ambient continuous bilinear map
   `(K,L) ↦ K * η * L` from `IsBilinearMap.toContinuousBilinearMap` in finite
   dimension, proves the quadratic term has zero strict derivative at the
   origin, codomain-restricts back to the symmetric submodule, and adds the
   affine-linear derivative `K ↦ 2K`.
2. Apply
   `HasStrictFDerivAt.toOpenPartialHomeomorph` to get an open partial
   homeomorphism `e` on `sourceSymmetricMatrixSubmodule r` with forward map
   `sourceHeadSliceGramPolynomial d r hrD`, source containing `0`, and target
   containing `sourceHeadMetricSymmSubmodule d r hrD`.  This chart and its
   source/target neighborhood lemmas are now checked as
   `sourceHeadSliceGramPolynomialOpenPartialHomeomorph`,
   `sourceHeadSliceGramPolynomial_zero_mem_chartSource`,
   `sourceHeadSliceGramPolynomial_center_mem_chartTarget`,
   `sourceHeadSliceGramPolynomial_chartSource_mem_nhds_zero`, and
   `sourceHeadSliceGramPolynomial_chartTarget_mem_nhds_center`.
3. Convert the target from the symmetric submodule to
   `SourceSymmetricMatrixCoord r` via
   `sourceSymmetricMatrixCoordToSubmodule.symm`.  Define
   `Head.U` as this converted target and define
   `Head.factor A` by pulling `A` back to the symmetric submodule, applying
   `e.symm`, and converting the resulting `K` to the slice point
   `sourceHeadGaugeSliceOfSymmCoord d r hrD K`.
4. Define `Head.factorDomain` as the preimage of the restricted chart source.
   The restriction intersects the raw IFT source with the fixed entrywise
   coordinate window
   `sourceSymmetricMatrixCoordinateWindow r
   (sourceHeadSliceGaugeIFTWindowRadius r)`.  Openness and center membership
   follow from the checked homeomorphism, the source membership of `0`, and
   the checked positivity of the radius.  The required coordinate-window field
   is checked as
   `sourceHeadSliceIFTFactorDomain_coordinate`, using
   `exists_sourceHeadGaugeSliceCoordinateWindow_subset_of_mem_nhds_center`.
5. The fields of `SourceRankDeficientHeadSliceGaugeData` are checked
   mechanically:
   `factor_continuousOn` is continuity of `e.symm` on the target composed with
   the checked homeomorphisms; `factor_center` is
   `e.symm (sourceHeadMetricSymmSubmodule d r hrD) = 0`; `factor_gram` is
   `OpenPartialHomeomorph.right_inv` plus
   `sourceHeadSliceGramPolynomial_eq_factorGram`; `factorDomain_mem` and
   `factor_left_inverse` are `map_source` and `left_inv` for `e`; and
   `factor_det_unit` follows by extracting the stored small coordinate-window
   membership from the restricted source, transporting it back to an identity
   window in the slice, and applying the checked Gershgorin estimate
   `sourceHeadGaugeSliceCoordinateWindow_det_isUnit`.

This transcript is the finite-dimensional local-inverse construction needed
for the sliced local-image producer.  It is independent of BHW continuation,
OS positivity, Wightman functions, and the later monodromy atlas.  The
coordinate-window neighborhood-basis helper, strict derivative, raw
`OpenPartialHomeomorph` packaging, determinant-unit shrink, left inverse, and
final structure fill are now checked in
`BHW.sourceRankDeficientHeadSliceGaugeData`.  This concrete producer is now
consumed by the checked canonical local-image wrapper
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.maxRankLocalImageData_of_headSliceIFTSchurWindow`,
so the canonical rank-deficient local-image packet no longer carries a free
`Head : SourceRankDeficientHeadSliceGaugeData d r hrD` parameter at its public
entry point.  The arbitrary exceptional-rank producer
`BHW.sourceOrientedRankDeficientMaxRankLocalImageData_of_headSliceIFT` is also
checked: it chooses the existing algebraic normal-form transport for `G0`,
uses the canonical `headSliceIFTSchurWindow` packet there, and transports the
result back to the requested neighborhood.  The hard-range connectedness
consumer now uses this producer directly in
`BHW.sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT`,
closing the previous rank-deficient-local-image hypothesis in the
finite-overlap topology layer.
The closed-loop finite-overlap domain constructors now also have
connected-domain forms,
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_positiveConnectedDomains_headSliceIFT`
and
`BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_zeroTransitions_headSliceIFT`.
The connected-domain forms take connected relatively open overlap/closing
domains and derive the needed max-rank connectedness internally from the
checked sliced-head IFT local-image producer.  The strongest checked surface
is now
   `exists_of_positivePreconnectedDomains_headSliceIFT`: it asks for the
   exact topological data produced by local source-normal-form shrinkage
   (`IsRelOpenInSourceOrientedGramVariety`, `IsPreconnected`, and
   `Nonempty`) plus the ordered containment fields.  The zero-transition edge
   case is completely mechanical as
   `exists_of_zeroTransitions_closedLoop_headSliceIFT`, because
   `BHWJostOrientedClosedContinuationLoop` already stores
   `closing_orientedPatch_preconnected` and
   `closing_orientedPatch_nonempty`.
   For a producer that does not want to split on `L.chain.m`, the checked
   `exists_of_preconnectedDomains_headSliceIFT` performs that case split:
   zero-transition loops use the stored closing patch, and positive loops use
   the supplied ordered preconnected domains.

   The final checked producer-facing interface is now
   `BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData`.  It stores
   only:
   `hn : d + 1 <= n`,
   relatively open nonempty preconnected `stepDomain j`,
   the containments
   `stepDomain j ⊆ (L.chain.localChart 0).orientedDomain`,
   `stepDomain j ⊆ (L.chain.localChart (Fin.castSucc j)).orientedDomain`,
   `(L.chain.oriented_transition j).orientedPatch ⊆ stepDomain j`,
   and the ordered next-domain containments; plus a relatively open nonempty
   preconnected `closingDomain` contained in the final and initial oriented
   chart domains, containing `L.closing_orientedPatch`, and containing the
   last transition patch in the positive-length case.  It deliberately has no
   `initialSeed` field and no max-rank-connectedness fields.  The checked
   method
   `BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.to_sourceMonodromy_headSliceIFT`
   is exactly:
   first call
   `BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_preconnectedDomains_headSliceIFT`,
   then apply
   `BHWJostOrientedClosedLoopFiniteOverlapDomainData.to_sourceMonodromy_headSliceIFT`.
   Therefore, if the remaining strict OS I §4.5 BHW/Jost construction
   produces a genuine large starting branch domain covering the finite-overlap
   ribbon, the producer theorem should output this preconnected data structure
   for the specific source-backed closed loop; once it does, monodromy is a
   mechanical one-line consumer.
   The stable public consumer name is checked as
   `BHW.bhw_jost_closedChain_sourceMonodromy_of_preconnectedFiniteOverlapData`:
   its proof is just `P.to_sourceMonodromy_headSliceIFT`.
   The degenerate zero-transition branch is also checked at this
   producer-facing level as
   `BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.exists_of_zeroTransitions`
   and
   `BHW.bhw_jost_closedChain_sourceMonodromy_of_zeroTransitions`: if
   `L.chain.m = 0`, the finite step family is empty and the stored
   `L.closing_orientedPatch` is the closing domain.
   A Gemini theorem-shape sanity check on 2026-05-06 agreed with the route
   discipline here: an arbitrary closed-loop statement from only `L` and
   `hn` is too strong, because chart intersections can have multiple
   components and the finite-overlap ribbon is supplied by the source-backed
   path/atlas construction, not by the abstract loop fields alone.
   Follow-up route audit on the same date flagged the load-bearing role of
   `stepDomain_sub_start`: the checked induction fixes
   `Φ := (L.chain.localChart 0).Psi`, so every positive-length step domain
   must genuinely lie in the starting oriented branch domain.  This is not a
   harmless bookkeeping field.  The strict BHW/Jost producer must either
   construct that large source-backed starting domain explicitly, or the
   positive-length theorem should target
   `BHWJostOrientedFiniteOverlapPropagationData L` directly via an
   accumulated-germ chain that carries the continued branch step by step.  In
   that patch-by-patch route, the terminal call is now checked as
   `P.to_sourceMonodromy_headSliceIFT`, with no detour through
   `stepDomain_sub_start`.  If the accumulated propagation reaches the closing
   oriented patch itself, the even smaller checked exit is
   `BHWJostOrientedClosingPatchTerminalSeedData L`, consumed by
   `BHW.bhw_jost_closedChain_sourceMonodromy_of_closingPatchTerminalSeedData`.
   No production theorem may infer `stepDomain_sub_start` from an arbitrary
   closed loop.

The first normal-parameter support layer is now checked in
`SourceOrientedNormalParameter.lean`.  The file supplies the finite head/tail
source-label split
`BHW.finSourceHead`, `BHW.finSourceTail`,
`BHW.finSourceHead_tail_cases`, injectivity/disjointness lemmas, the finite
normal parameter record
`BHW.SourceOrientedRankDeficientNormalParameter`, the induced coordinate
topology and continuous projections
`BHW.continuous_sourceOrientedNormalParameterCoord`,
`BHW.continuous_sourceOrientedNormalParameter_head`,
`BHW.continuous_sourceOrientedNormalParameter_mixed`, and
`BHW.continuous_sourceOrientedNormalParameter_tail`, the checked finite-product
coordinate equivalence and topology bridge
`BHW.sourceOrientedNormalParameterCoordEquiv` and
`BHW.sourceOrientedNormalParameterCoordHomeomorph`, the single finite-function
coordinate model
`BHW.SourceOrientedNormalParameterFiniteCoordIndex`,
`BHW.sourceOrientedNormalParameterFiniteCoord`,
`BHW.sourceOrientedNormalParameterFiniteCoordEquiv`,
`BHW.sourceOrientedNormalParameterFiniteCoordHomeomorph`,
`BHW.sourceOrientedNormalParameterFiniteCoordBall`, and
`BHW.sourceOrientedNormalParameterFiniteCoordBall_open_connected_center`, the
checked pullback parameter ball
`BHW.sourceOrientedNormalParameterBall`,
`BHW.sourceOrientedNormalParameterBall_open_connected_center`,
`BHW.exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center`, and
`BHW.exists_sourceOrientedNormalParameterBall_subset_head_det_isUnit`, the
transported open-neighborhood shrink
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.exists_normalParameterBall_image_subset_open_and_head`,
the
checked open
invertible-head locus and center-neighborhood theorem
`BHW.isOpen_sourceOrientedNormalParameter_head_det_isUnit` and
`BHW.sourceOrientedNormalParameter_head_det_isUnit_mem_nhds_center`, its center
`BHW.sourceOrientedNormalCenterParameter`, the padded tail embedding
`BHW.sourceTailEmbed`, the canonical normal source
`BHW.hwLemma3CanonicalSource`, the checked signature head metric
`BHW.sourceHeadMetric`, its symmetry theorem
`BHW.sourceHeadMetric_transpose`, its determinant-unit theorem
`BHW.sourceHeadMetric_det_isUnit`, the canonical head-Gram identity
`BHW.sourceMinkowskiGram_hwLemma3CanonicalSource_head`, the derived canonical
head-block unit theorem `BHW.hwLemma3CanonicalSource_head_unit`, the vector
bilinear form `BHW.sourceVectorMinkowskiInner`, the shifted residual-tail
metric and Gram coordinates `BHW.sourceTailMetric`,
`BHW.sourceTailMetric_det_isUnit`, the explicit diagonal normalizing scalars
`BHW.sourceTailMetricScale`, `BHW.sourceTailMetricScale_ne_zero`,
`BHW.sourceTailMetricScale_mul_self`, `BHW.sourceTailMetricScale_norm`,
`BHW.sourceTailMetricDetScale`, `BHW.sourceTailMetricDetScale_ne_zero`, and
`BHW.sourceTailMetricDetScale_norm`, the checked full-frame head-tail
embedding `BHW.sourceFullFrameEmbeddingOfHeadTail` with its head/tail
evaluation theorems, the checked head/tail sum equivalence
`BHW.sourceHeadTailSumEquiv` with its inl/inr evaluation theorems, and
`BHW.sourceShiftedTailGram`, the checked shifted-tail oriented data and
projection API `BHW.SourceShiftedTailOrientedData`,
`BHW.sourceShiftedTailOrientedInvariant`,
`BHW.sourceShiftedTailOrientedInvariant_gram`, and
`BHW.sourceShiftedTailOrientedInvariant_det`, the checked
head/head normal parameter Gram formula
`BHW.sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector`, the checked
head/tail orthogonality and mixed-block formulas
`BHW.sourceVectorMinkowskiInner_headVector_sourceTailEmbed`,
`BHW.sourceVectorMinkowskiInner_sourceTailEmbed_headVector`,
`BHW.sourceVectorMinkowskiInner_head_tailParameterVector`, and
`BHW.sourceVectorMinkowskiInner_tailParameterVector_head`, the checked
head-Gram symmetry theorem `BHW.sourceNormalHeadGram_transpose`, the checked
mixed-head/tail helper formulas
`BHW.sourceVectorMinkowskiInner_mixedHeadPart_sourceTailEmbed`,
`BHW.sourceVectorMinkowskiInner_sourceTailEmbed_mixedHeadPart`, and
`BHW.sourceVectorMinkowskiInner_mixedHeadPart_mixedHeadPart`, the checked
tail/tail normal-parameter formula
`BHW.sourceVectorMinkowskiInner_tailParameterVector_tail`, the head-vector and
full normal-parameter maps, their head/tail evaluation equations, and their
continuity theorems
`BHW.continuous_sourceOrientedNormalHeadVector` and
`BHW.continuous_sourceOrientedNormalParameterVector`, and the checked center
theorems
`BHW.sourceOrientedNormalHeadVector_center` and
`BHW.sourceOrientedNormalParameterVector_center`.  The ordinary Gram-coordinate
part of the normal Schur reconstruction is now reduced to exact checked block
formulas.  The next nontrivial Lean target is the determinant-coordinate
expansion plus the shifted-tail realization packet needed for the full
`sourceOrientedNormalParameterVector_realizes_schur` theorem.

Tail-signature readiness correction: the residual tail in this normal form is
not allowed to silently use the Euclidean tail dot product on
`Fin (d + 1 - r)`.  It inherits the shifted full metric
`MinkowskiSpace.metricSignature d (finSourceTail (Nat.le_of_lt hrD) μ)`;
for `0 < r`, the time direction has already been selected into the head block.
The proof docs now require shifted-tail oriented data
`SourceShiftedTailOrientedData`, shifted invariant
`sourceShiftedTailOrientedInvariant`, and shifted one-way small realization
together with a local normal-parameter radius choice.  The existing standard
tail-realization theorem may be consumed only through an explicit finite
diagonal normalization
equivalence that rescales determinant coordinates by the product of the
coordinate scalars.  The scalar and product nonzero facts are now checked as
`sourceTailMetricScale_ne_zero` and `sourceTailMetricDetScale_ne_zero`;
otherwise the Euclidean theorem proves the wrong tail theorem.
The finite normalization layer is now checked in
`SourceOrientedTailEuclidean.lean`: `SourceTailOrientedData`,
`sourceTailOrientedInvariant`, `sourceTailOrientedVariety`,
`sourceTailPermuteOrientedData`, `sourceTailOrientedInvariant_perm`,
`sourceTailOrientedVariety_perm_iff`,
`SourceShiftedTailMetricNormalization`,
`sourceShiftedTailMetricNormalization`,
`sourceShiftedTailDataToEuclidean`,
`sourceShiftedTailInvariant_toEuclidean`,
`sourceShiftedTailVariety_toEuclidean_iff`,
`sourceShiftedTailDataToEuclidean_injective`, and
`sourceShiftedTailInvariant_eq_of_toEuclidean_eq`.  The older
estimate-compatible packet wrappers are also checked there as data/converter
infrastructure:
`SourceTailOrientedCompatibleSmallRealization`,
`SourceShiftedTailCompatibleSmallRealization`, and
`sourceShiftedTailCompatibleSmallRealization_of_euclidean`.  They are not the
active local-image dependency.  The active shifted theorem is
`sourceShiftedTailSmallRealization` in
`SourceOrientedTailSmallRealization.lean`: it builds the explicit
normalization, calls the checked Euclidean one-way theorem on
`sourceShiftedTailDataToEuclidean T`, scales the realizing tuple back by
`scale⁻¹`, uses the norm-one scale lemmas for the realization estimate, and
uses `sourceShiftedTailInvariant_eq_of_toEuclidean_eq` to recover the shifted
invariant equality.  The normal Schur chart must choose its parameter tail
radius and residual-data radius in one local finite-dimensional estimate
theorem; it must not obtain forward containment by destructing an abstract
existential one-way theorem and hoping the returned radius has a compatible
size.  The first Euclidean induction case is checked:

The source-oriented adapter for a supplied compatible shifted-tail packet is
checked in `SourceOrientedRankDeficientTailRadius.lean`; it defines
`BHW.SourceOrientedSchurTailSmallFor`,
`BHW.SourceOrientedRankDeficientTailRadiusChoice`, and
`BHW.SourceOrientedRankDeficientTailRadiusChoice.ofShiftedCompatible`.  This
adapter is now recorded only as conditional bookkeeping, not as an active
existence target.  A same-radius packet with one tail coordinate radius
`ε` and one residual-data radius `η` is not the correct general local-image
shape: for the quadratic tail Gram map, coordinate polydiscs and invariant
polydiscs do not give a bidirectional box in general tail dimension.  The
active proof must instead use a target-shaped tail window.  Choose a tail
coordinate radius `ε` and obtain a residual-data radius `η` from the checked
one-way theorem `sourceShiftedTailSmallRealization`; then define the connected
normal-parameter set by the raw head/mixed/tail coordinate bounds **and** the
explicit condition
`sourceShiftedTailOrientedInvariant p.tail` has all Gram and determinant
coordinates `< η`.  Forward containment of the parameter set into the Schur
neighborhood is then part of the definition of the window, while reverse
Schur extraction uses `sourceShiftedTailSmallRealization` to produce a tail
tuple satisfying both the coordinate bound and the invariant-window bound.
The window is open by finite-coordinate continuity and connected because it
is star-shaped from the normal center: along `t ∈ [0,1]`, head/mixed/tail
coordinates scale toward the center, tail Gram coordinates scale by `t^2`,
and tail determinant coordinates scale by `t^(d+1-r)`.
The Lean support for this corrected shape is checked in
`SourceOrientedRankDeficientTailWindow.lean`: it defines
`BHW.SourceOrientedRankDeficientTailWindowChoice`,
`BHW.sourceOrientedRankDeficientTailWindow`,
`BHW.sourceMatrixCoordinateWindow`,
`BHW.sourceOrientedHeadCoordinateWindow`,
`BHW.sourceOrientedMixedCoordinateWindow`,
`BHW.sourceShiftedTailTupleWindow`,
`BHW.isOpen_sourceShiftedTailTupleWindow`,
`BHW.isConnected_sourceShiftedTailTupleWindow`,
`BHW.isOpen_sourceOrientedRankDeficientTailWindow`,
`BHW.sourceOrientedNormalCenterParameter_mem_tailWindow`,
`BHW.sourceOrientedRankDeficientSchurParameterWindow`,
`BHW.sourceOrientedRankDeficientSchurParameterWindow_open_connected`,
`BHW.sourceOriented_rankDeficient_tailWindowChoice`, and
`BHW.SourceOrientedRankDeficientTailWindowChoice.normalParam_tail_small`.
The pure shifted-tail tuple window is checked open and connected; connectedness
uses the homogeneity lemmas
`BHW.sourceShiftedTailGram_smul`,
`BHW.sourceShiftedTailOrientedInvariant_smul_gram`, and
`BHW.sourceShiftedTailOrientedInvariant_smul_det`.  The full Schur parameter
window is now checked as the finite product assembly of the identity head
coordinate polydisc, the zero mixed-coordinate polydisc, and the shifted-tail
tuple window, transported through the checked normal-parameter coordinate
homeomorphism.  The remaining rank-deficient local-image work is therefore the
Schur/residual image and shrink theorem, not the connectedness of the
parameter window and not a compatible-radius estimate.
The max-rank-slice topology of this same window is now split at the correct
frontier by
`BHW.isConnected_sourceOrientedRankDeficientSchurParameterWindow_tailRank`:
connectedness of the full Schur-parameter window restricted to residual-tail
exact rank follows from connectedness of the tail-coordinate exact-rank slice.
The first upstream residual-tail bridge is now checked in
`SourceOrientedRankDeficientTailRankConnected.lean`:
`BHW.sourceComplexDotGram_rank_eq_iff_fullRank` identifies exact ordinary
dot-Gram rank with full column rank of the tuple,
`BHW.sourceShiftedTailGram_rank_eq_iff_normalized_fullRank` transports this
through the norm-one diagonal normalization from the shifted tail metric to the
Euclidean dot product, and
`BHW.sourceShiftedTailTupleWindow_tailRank_joined_radial_smul` proves that
positive radial shrinking stays inside the target-shaped shifted-tail window
and preserves exact residual rank.  The file now also checks
`BHW.sourceFullRankConfigurations_smul_mem`,
`BHW.real_pow_le_self_of_pos_of_le_one`,
`BHW.sourceShiftedTailTupleWindow_tailRank_joined`,
`BHW.sourceShiftedTailTupleWindow_tailRank_nonempty`,
`BHW.isPathConnected_sourceShiftedTailTupleWindow_tailRank`, and
`BHW.isConnected_sourceShiftedTailTupleWindow_tailRank`.

The checked proof is exactly the planned transcript.  In the hard range
`hn : d + 1 ≤ n`, set `D := d + 1 - r`, `m := n - r`, and derive
`D ≤ m`.  For two tail-slice points, normalize by
`Aᵢ u μ := (sourceShiftedTailMetricNormalization d r hrD).scale μ * qᵢ u μ`.
The rank bridge puts `Aᵢ` in `sourceFullRankConfigurations m D`; the checked
path-connectedness of that full-rank configuration space gives a path `γ`.
Unnormalize `γ`, bound the unnormalized tuple, shifted Gram, and determinant
paths on `unitInterval`, choose one `0 < ρ ≤ 1` small enough for both the
coordinate and residual-data radii, join the endpoints radially, and use
`t ↦ ρ • γq t` for the middle path.  Coordinate bounds use the tuple norm
bound; Gram and determinant bounds use the checked homogeneity lemmas and
`ρ^D ≤ ρ`; exact rank uses normalized full-rank preservation under nonzero
scalar multiplication.  A separately constructed scaled standard full-rank
configuration proves nonemptiness.  Thus the residual-tail exact-rank
connectedness blocker is closed with no new axiom or `sorry`.

The first Euclidean induction case is checked:
`sourceTailOrientedInvariant_selectedGram_det` proves that a selected Gram
determinant is the square of the selected tail determinant,
`sourceTailOrientedVariety_det_eq_zero_of_gram_eq_zero` proves zero Gram
forces all top determinants to vanish in positive tail dimension, and
`sourceTailOrientedSmallRealization_zeroGram` realizes such data by the zero
tail tuple.  The estimate wrapper
`sourceTailOrientedSmallRealization_zeroRank_bound` is checked too: rank zero
is converted to zero Gram and then realized by the zero tuple with an arbitrary
positive `epsilon`.

Determinant-readiness correction: the proof docs now pin determinant recovery
for the normal parameter vector as explicit finite theorem surfaces and record
that determinant recovery depends on the chosen head factor, not only on the
head Gram block.  `SourceOrientedSchurResidualData` must store
`headFactor` with
`headFactor * sourceHeadMetric d r hrD * headFactor.transpose = A`, and the
full reconstruction theorem must require `p.head = R.headFactor`; the weaker
Gram equality is insufficient for determinant coordinates.  The primitive
selected-frame calculation is
`sourceFullFrameDet_normalParameter_headTail`, using the embedding
`sourceFullFrameEmbeddingOfHeadTail`; it proves that frames containing the
selected head block have determinant
`p.head.det * (sourceShiftedTailOrientedInvariant ... p.tail).det lam`.
The blueprint now pins this selected-frame theorem to an explicit
`sourceHeadTailSumEquiv` reindexing surface and mathlib's
`Matrix.det_fromBlocks_zero₁₂`: after reindexing the selected full-frame
matrix is exactly
`Matrix.fromBlocks p.head 0 ((p.mixed.submatrix lam id) * p.head)
  (fun u μ => p.tail (lam u) μ)`, and this block identification is now
checked as `BHW.sourceFullFrameMatrix_normalParameter_headTail_blocks`.
Taking determinants gives the checked raw selected-frame theorem
`BHW.sourceFullFrameDet_normalParameter_headTail_raw`; the remaining
shifted-tail wrapper is now checked as
`BHW.sourceFullFrameDet_normalParameter_headTail` using
`sourceShiftedTailOrientedInvariant_det`.  The arbitrary-frame Schur formula
has also started in Lean with checked definitions
`BHW.sourceNormalFullFrameCoeff`, `BHW.sourceNormalFullFrameHeadBlock`, and
`BHW.sourceNormalFullFrameTailBlock`,
`BHW.sourceNormalFullFrameTailRowsDet`, and
`BHW.sourceNormalFullFrameDetFromSchur`, plus the checked bridge theorem
`BHW.sourceNormalFullFrameTailRowsDet_eq_det_tailBlock`.  The coefficient and
block evaluation lemmas, the two normal-parameter coordinate projection
theorems, and the arbitrary-frame matrix identity
`BHW.sourceFullFrameMatrix_normalParameter_eq_blockColumns` are also checked.
Most importantly, the finite determinant blocker is now discharged in Lean.
`BHW.matrix_det_blockColumn_laplace` proves the ordinary row-subset Laplace
expansion for `BHW.matrixBlockColumns` by an exterior-algebra top-coordinate
argument, and
`BHW.sourceFullFrameDet_normalParameter_eq_schurFormula` is now the
unconditional normal-parameter determinant reconstruction theorem.  The
conditional theorem
`BHW.sourceFullFrameDet_normalParameter_eq_schurFormula_of_laplace` remains as
a checked reusable bridge, but its hypothesis is now supplied by
`BHW.matrix_det_blockColumn_laplace`.  The finite Laplace bookkeeping now
uses checked ordered-row-subset definitions
`BHW.matrixBlockColumns`, `BHW.matrixBlockColumns_inl`,
`BHW.matrixBlockColumns_inr`, `BHW.matrixBlockColumns_reindex_finSum`,
`BHW.matrixRowSubset_compl_card`,
`BHW.matrixRowSubsetHeadRows`, `BHW.matrixRowSubsetTailRows`,
`BHW.matrixRowSubsetSumEquiv`, `BHW.matrixRowSubsetLaplaceSign`,
`BHW.matrixBlockColumnLaplaceTerm`, and
`BHW.matrixBlockColumnLaplaceSum`, with row subsets represented by
`Set.powersetCard` to match mathlib's exterior-algebra basis.  The checked
exterior support lemmas include
`BHW.matrixBlockColumns_iMulti_eq_mul`,
`BHW.exteriorPower_repr_iMulti_matrixColumns`,
`BHW.exteriorAlgebra_repr_of_mem`,
`BHW.powersetCard_univ_orderEmb_id`,
`BHW.exteriorAlgebra_top_repr_iMulti_matrixColumns`,
`BHW.exteriorAlgebra_iMulti_matrixColumns_eq_sum_minors`, and
`BHW.exteriorAlgebra_basis_mul_iMulti_compl_repr`.  The determinant work over
`G` is therefore no longer finite row algebra; it is the oriented source-variety
propagation equality `sourceOrientedSchur_fullFrameDet_reconstruct`, now
checked in `SourceOrientedSchurPropagation.lean`.
The Schur residual coordinate packet consuming this determinant algebra is now
also checked in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedSchurResidual.lean`:
`BHW.sourceOrientedSchurHeadBlock`,
`BHW.sourceOrientedSchurHeadBlock_apply`,
`BHW.sourceOrientedSchurMixedBlock`,
`BHW.sourceOrientedSchurTailBlock`, `BHW.sourceSchurMixedCoeff`,
`BHW.sourceSchurMixedCoeff_mul_headBlock`, `BHW.sourceSchurComplement`,
`BHW.sourceSchurResidualDeterminants`,
`BHW.sourceShiftedTailOrientedVariety`,
`BHW.SourceOrientedSchurResidualData`,
`BHW.SourceOrientedSchurResidualData.L_mul_A`,
`BHW.sourceVectorMinkowskiInner_comm`,
`BHW.sourceVectorMinkowskiInner_sub_left`,
`BHW.sourceVectorMinkowskiInner_sub_right`,
`BHW.sourceActualSchurResidualVector`,
`BHW.sourceActualSchurResidualVector_decomp`,
`BHW.sourceActualSchurResidualVector_inner_head`,
`BHW.sourceActualSchurResidualVector_head_inner`,
`BHW.sourceActualSchurResidualVector_inner_residual`,
`BHW.sourceActualSchurSelectedOriginalMatrix`,
`BHW.sourceActualSchurSelectedResidualMatrix`,
`BHW.sourceSchurHeadTailRowOperation`,
`BHW.sourceSchurHeadTailRowOperation_det`,
`BHW.sourceActualSchurSelectedResidualMatrix_eq_rowOperation_mul`,
`BHW.sourceActualSchurResidual_selectedFrameDet`,
`BHW.sourceActualSchurResidual_selectedFrameDet_eq_headFactor_mul_tail_det`,
`BHW.sourceOrientedNormalParameterVector_realizes_schur_gram`,
`BHW.sourceNormalFullFrameDetFromSchur_headTail`,
`BHW.sourceNormalFullFrameDetFromSchur_headTail_eq_source_det`,
`BHW.sourceOrientedSchur_fullFrameDet_reconstruct_of_headTailPropagation`, and the
checked determinant consumer
`BHW.sourceOrientedNormalParameterVector_realizes_schur_det_of_fullFrameReconstruct`
together with the full oriented-data consumer
`BHW.sourceOrientedNormalParameterVector_realizes_schur_of_fullFrameReconstruct`.
That consumer deliberately kept the genuine Plucker/Cauchy-Binet
reconstruction theorem as an explicit hypothesis until the propagation theorem
was checked.  The checked hard-range
`sourceOrientedSchur_fullFrameDet_reconstruct` theorem takes
`hGvar : G ∈ sourceOrientedGramVariety d n`; without this range hypothesis,
the unselected determinant coordinates of the product-coordinate datum `G` are
arbitrary and the reconstruction statement is false.  Thus arbitrary ordered
full frames are routed through the finite Laplace theorem
`matrix_det_blockColumn_laplace`, `sourceNormalFullFrameDetFromSchur`,
`sourceFullFrameDet_normalParameter_eq_schurFormula`, and the checked
`sourceOrientedSchur_fullFrameDet_reconstruct`.  Its selected head-tail
specialization is already checked by
`sourceNormalFullFrameDetFromSchur_headTail_eq_source_det`, using
`R.tail_det_eq` and cancellation by `R.headFactor_det_unit`.  The actual
residual Gram theorem is also now checked: for an actual representative `z`,
`sourceActualSchurResidualVector_inner_residual` proves that the projected
tail residuals have Gram matrix `R.tail.gram`.  The selected actual-residual
row-operation theorem is checked too:
`sourceActualSchurResidual_selectedFrameDet` packages the determinant-one block
lower-triangular row operation that replaces selected tail rows by actual
Schur residual rows without changing the selected full-frame determinant, and
`sourceActualSchurResidual_selectedFrameDet_eq_headFactor_mul_tail_det`
combines it with `R.tail_det_eq` to prove the exact selected calibration
`det(actual head + actual residual_lam) = R.headFactor.det * R.tail.det lam`.
The arbitrary-frame reconstruction is routed through an oriented-variety
determinant propagation theorem, not through a row-operation shortcut.  The
checked selected row-operation theorem is only the calibration case where the
chosen frame contains the whole head block; it is not a valid shortcut for
arbitrary ordered full frames.  Gemini was consulted on 2026-05-05 and agreed
that the missing theorem was precisely an oriented residual-volume
uniqueness/propagation input; it also warned that a Gram-only comparison and a
naive arbitrary-frame row-operation argument are false.  The hard input is now
isolated as
`sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq`: if two points of
`sourceOrientedGramVariety d n` have the same Gram coordinate, an invertible
selected head Gram block, and matching determinant coordinates on every
selected `head ∪ lam` frame, then their full determinant-coordinate functions
are equal.  The determinant-nonzero branch of this input is already checked in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedSchurPropagation.lean`
as
`sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_exists_nonzero`:
if some selected `head ∪ lam` determinant is nonzero, it reduces to the
existing full-frame chart identity
`sourceOrientedGramData_eq_of_selectedCoord_eq_mixedRows_eq`.  Thus the only
other branch of the propagation input is the low-rank case where every
selected head-tail full-frame determinant vanishes.  The low branch is now
closed in checked Lean by the rank-theoretic bridge
`sourceOrientedGramVariety_det_eq_zero_of_not_maxRank` and the conditional
assembly theorem
`sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_allZero_notMaxRank`.
The first says that any source-variety point outside the oriented max-rank
locus has all full-frame determinant coordinates zero, because a single
nonzero determinant would imply `SourceOrientedMaxRankAt` by the checked
full-frame producer.  The second says that the full propagation theorem follows
from the following now-checked hard-range lemma:

```lean
theorem BHW.sourceOrientedGramVariety_notMaxRank_of_headTailDet_eq_zero
    (d n r : Nat)
    (hn : d + 1 <= n)
    (hrD : r < d + 1)
    (hrn : r <= n)
    {G : BHW.SourceOrientedGramData d n}
    (hG : G ∈ BHW.sourceOrientedGramVariety d n)
    (hA :
      IsUnit (BHW.sourceOrientedSchurHeadBlock n r hrn G).det)
    (hzero :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        G.det
          (BHW.sourceFullFrameEmbeddingOfHeadTail
            d n r hrD hrn lam) = 0) :
    ¬ BHW.SourceOrientedMaxRankAt d n G
```

This lemma is now checked in
`SourceOrientedSchurPropagation.lean`.  Its proof uses the contrapositive:
if `G` is max-rank and the selected head Gram block is invertible, then some
selected `head ∪ lam` full-frame determinant is nonzero.  The finite
basis-extension theorem is also checked there as
`exists_headTail_fullFrameDet_ne_zero_of_headRows_linearIndependent_span_top`:
after quotienting the source span by the head-row span, choose a linearly
independent quotient basis from the tail images and lift it to tail labels.
Together with
`sourceHeadRows_linearIndependent_of_schurHeadBlock_isUnit`, this proves
`sourceOrientedGramVariety_notMaxRank_of_headTailDet_eq_zero`, closes the
all-zero branch, and gives the hard-range theorem
`sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq`.  The checked theorem
`sourceOrientedSchur_fullFrameDet_reconstruct_of_headTailPropagation` proves
that this one propagation theorem mechanically gives the Schur full-frame
determinant reconstruction by building the normal parameter from `R.tail_mem`,
calling the checked Gram realization theorem, checking selected head-tail
determinants, and rewriting through
`sourceFullFrameDet_normalParameter_eq_schurFormula`.  The no-hypothesis
hard-range wrappers are also checked:
`sourceOrientedSchur_fullFrameDet_reconstruct`,
`sourceOrientedNormalParameterVector_realizes_schur_det`, and
`sourceOrientedNormalParameterVector_realizes_schur`.  No downstream proof may
use an unnamed "block determinant expansion" anymore.  The next producer-level
normal-form bridge is also now checked in `SourceNormalFormTransport.lean`:
`sourceOriented_lowRank_exists_normalFormSourceMatrix_to_canonical` selects an
adapted representative, nonzero principal rank minor, source permutation,
Schur complement, head-metric congruence, and Witt/Lorentz normalization to
produce an invertible source-label matrix sending any exceptional oriented
source-variety point to the canonical Lemma-3 invariant.  Its
variety-relative consumer
`sourceOriented_lowRank_exists_normalFormVarietyTransport_from_canonical`
packages the same result as a `SourceOrientedVarietyTransportEquiv` whose
inverse carries `hwLemma3CanonicalSourceOrientedVariety` back to the original
point.  The small companion file
`SourceOrientedRankDeficientAlgebraicNormalForm.lean` now exposes this as the
producer-facing data packet
`SourceOrientedRankDeficientAlgebraicNormalFormData` and constructor
`sourceOriented_rankDeficient_algebraicNormalFormData`.  This is the transport
interface for the rank-deficient local-image producer; the old ambient
`SourceOrientedInvariantTransportEquiv` normal-form shortcut remains rejected.
The next producer-level target is the concrete Schur/residual local-image
construction around that canonical center, starting with the
existence/construction of the `SourceOrientedSchurResidualData` packet from a
nearby source-variety point with an invertible selected head block.
The canonical-center head-gauge facts are now checked in
`SourceOrientedRankDeficientCanonical.lean`:
`sourceOrientedSchurHeadBlockSymm_canonical` identifies the canonical head
block with `sourceHeadMetricSymmCoord`, `hwLemma3CanonicalSource_headGauge_mem`
puts that center in every local head gauge by `Head.center_mem`, and
`sourceOriented_canonical_headGaugeNormalParameterData` instantiates the
checked Witt/head-normalization consumer at the canonical center.  The local
image producer can therefore start from an honest centered head-gauge chart,
not from an abstract or global square-root branch.
The next subtype-valued transport layer is also checked in
`SourceOrientedRankDeficientNormalImage.lean`: the normal-parameter map
`sourceOrientedNormalParameterVarietyPoint` lands in
`SourceOrientedVariety d n`, is continuous, and sends
`sourceOrientedNormalCenterParameter` to
`hwLemma3CanonicalSourceOrientedVariety`; for any algebraic normal-form packet
`N`, `N.originalNormalVarietyPoint` is the inverse-transported normal image,
is continuous, is centered at the original exceptional point, and rewrites
max-rank through `N.varietyTransport.invFun_maxRank_iff`.  This removes the
remaining ambient-transport placeholder from the local-image producer surface.
On the invertible-head part of the normal-parameter box, the same file proves
`sourceOrientedNormalParameterVarietyPoint_gram_sourcePrincipalSchurGraph` and
`sourceOrientedNormalParameterVarietyPoint_eq_sourcePrincipalSchurGraph`, so the
normal point supplies the exact `hnormal` equality required by
`isConnected_sourcePrincipalSchur_varietyTransported_orientedMaxRank_preimage_of_eq`.
It also proves
`SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint_maxRank_iff_tail_rank`:
after inverse transport from canonical normal form, and under the checked
invertible-head condition, oriented max-rank of the original normal image is
equivalent to exact rank `d + 1 - N.r` of the shifted residual-tail Schur
coordinate.  The downstream parameter connectedness proof can therefore rewrite
the max-rank slice directly as the exact-rank residual-tail cone; it no longer
needs to reopen the source-change transport or determinant-coordinate layer.
The set-level version
`BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.parameterBox_maxRank_preimage_eq_tailRank`
is now checked too: for any parameter box contained in the invertible-head
locus, its max-rank preimage under `N.originalNormalVarietyPoint` is literally
the same subset as the residual-tail exact-rank slice.  The remaining
connectedness proof may therefore focus only on the tail-rank geometry inside
the chosen Schur window.

- `BHW.same_sourceOrientedInvariant_detOneOrbit_or_singularLimit`, including
  the high-rank determinant-ratio/Witt-extension orbit theorem and the
  low-rank Hall-Wightman isotropic contraction data;
- checked `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected`, including
  the full-frame oriented local section, the arbitrary complex max-rank chart
  `BHW.sourceOrientedMaxRankChart_at`, their shared
  `BHW.SourceOrientedFullFrameMaxRankChartData` producer, and the
  rank-deficient Schur/residual realization chart;
- `BHW.sourceOrientedVarietyGermHolomorphicOn_extendF_descent`, including
  quotient-value continuity/local boundedness at the exceptional locus,
  analytic exceptional-rank codimension, oriented invariant-ring normality, and
  the normal analytic-space Riemann extension;
- the oriented real-patch uniqueness producer
  `BHW.sourceOrientedDistributionalUniquenessPatch_of_HWRealEnvironment`,
  whose local chart/totally-real identity theorem, tangent-complexification
  packet, and determinant-regular real subpatch producer are now
  componentwise pinned, with production Lean not started;
- the OS I §4.5 compact Figure-2-4 branch-difference theorem
  `BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45` and
  its source-patch compact partition.

Until the lower support lemmas in these five groups are implemented or
replaced by already checked sorry-free local support with the same
mathematical content, public theorem-2 Lean remains closed.  If Lean work
starts from this proof-doc state, the first target must be one of those lower
finite-dimensional, SCV, or OS-I support lemmas, not a public
scalar-representative or adjacent `S'_n` wrapper.

First lower Lean implementation step, 2026-05-02: the finite oriented
determinant layer is now checked in
`OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOriented.lean`
and exported by the `BHWPermutation` aggregate.  It introduces
`SourceOrientedGramData` as a product-coordinate abbreviation, so the oriented
source ambient space inherits the finite-dimensional complex normed
vector-space structure needed by later germ-holomorphic `DifferentiableOn`
statements.  It also introduces `sourceFullFrameMatrix`,
`sourceFullFrameDet`, `sourceOrientedMinkowskiInvariant`, and
`sourcePermuteOrientedGram`, and proves the
determinant/permutation/proper-complex-Lorentz support:
`continuous_sourceOrientedGramData_mk`,
`continuous_sourceMinkowskiGram`,
`continuous_sourceOrientedMinkowskiInvariant`,
`continuous_sourceFullFrameDet`,
`continuous_sourcePermuteOrientedGram`,
`differentiable_sourcePermuteOrientedGram`,
`sourceFullFrameDet_complexLorentzAction`,
`sourceFullFrameDet_permAct`,
`sourceMinkowskiGram_complexLorentzAction`,
`sourceOrientedMinkowskiInvariant_complexLorentzAction`, and
`sourceOrientedMinkowskiInvariant_permAct`.  The same file now also checks the
base oriented source-variety/double-domain scaffolding:
`sourceOrientedGramVariety`, `sourceOrientedExtendedTubeDomain`,
`sourceOrientedExtendedTubeDomain_subset_variety`,
`sourcePermuteOrientedGram_mem_variety_iff`,
`IsRelOpenInSourceOrientedGramVariety.preimage_sourcePermuteOrientedGram`,
`IsRelOpenInSourceOrientedGramVariety.inter`,
`IsRelOpenInSourceOrientedGramVariety.iUnion`,
`sourceOrientedDoublePermutationDomain_one_eq`,
`sourceOrientedDoublePermutationDomain_relOpen_of_sourceOrientedExtendedTubeDomain`,
and `sourceOrientedExtendedTubeDomain_connected`.  The oriented germ API is
also checked at the same lower layer:
`SourceOrientedVarietyGermHolomorphicOn`,
`SourceOrientedVarietyGermHolomorphicOn.continuousOn`,
`SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen`,
`SourceOrientedVarietyGermHolomorphicOn.sub`, and
`SourceOrientedVarietyGermHolomorphicOn.precomp_sourcePermuteOrientedGram`.
This is a genuine lower support layer, not a public theorem-2 wrapper.  It
closes only the mechanical finite topology/permutation/germ-API part of the
oriented route; public scalar-representative and adjacent `S'_n` Lean remains
closed until the remaining branch-law, relative-openness, descent, normality,
real-uniqueness, and OS-I compact producer groups below are implemented or
replaced by already checked support with the same mathematical content.

Local Figure-2-4 source-patch refinement, 2026-05-02: the false
`xseed_time0` field has been removed from the canonical source-patch proof
docs.  The checked geometry support now supplies
`BHW.os45CommonEdgeRealPoint_one_eq_self_of_time_zero`,
`BHW.os45CommonEdgeRealPoint_one_mem_orderedSector_of_mem`, and
`BHW.exists_ordered_small_time_perturb_with_commonEdge_in_adjacent_overlap_of_lt`
in `OSToWightmanLocalityOS45Figure24.lean`.  The same file now also checks
`BHW.continuous_adjacentTimePerturb_realParam`,
`BHW.adjacentTimePerturb_mem_identity_sector_of_pos`,
`BHW.os45CommonEdgeRealPoint_one_adjacentTimePerturb_eq_half`,
`BHW.adjacentTimePerturb_segment_commonEdge_subset_paramInterval`, and
`BHW.exists_ordered_small_time_perturb_with_commonEdge_segment_in_adjacent_overlap_of_lt`.
The strengthened perturbation chooses the ordered seed inside the overlap and
proves that the whole segment from the seed to its identity common-edge
contact lies in the overlap and both ordered sectors; the segment proof uses
only the explicit perturbation ray and does not assume convexity of
`ExtendedTube`, `Ufig`, or `Upath`.  Together with the checked topology helper
`BHW.exists_connected_open_precompact_subset_pair` in
`OSToWightmanLocalityOS45TraceMembership.lean`, this closes the local
two-point contact-and-shrink subgap for the later canonical source-patch
carrier, but not any scalar-source representative theorem.

Certified finite real-patch Lean target, 2026-05-02: after the checked
canonical source patch and its public accessors, the following layer is
mathematically complete and implementation-ready because it is only finite
point relabelling:
`BHW.os45SourcePermutationHomeomorph`,
`BHW.os45Figure24CompactRealPatch`,
`BHW.os45Figure24CompactRealPatch_open`,
`BHW.os45Figure24CompactRealPatch_nonempty`,
`BHW.os45Figure24CompactRealPatch_commonEdge_contact`,
`BHW.os45Figure24CompactRealPatch_jost`,
`BHW.os45Figure24CompactRealPatch_left_sector`, and
`BHW.os45Figure24CompactRealPatch_right_sector`.  The homeomorphism is
`u ↦ fun k μ => u (π.symm k) μ`, with inverse
`x ↦ fun k μ => x (π k) μ`; openness is
`Homeomorph.isOpenMap`, Jost membership is
`BHW.jostSet_permutation_invariant π.symm`, and sector membership is just the
definition of `BHW.permutedExtendedTubeSector`.  The contact point is
`os45SourcePermutationHomeomorph d n π P.xcontact`, where the checked
canonical packet proves
`P.xcontact = os45CommonEdgeRealPoint 1 P.xseed`,
`P.xseed ∈ os45Figure24SourcePatch`, and
`P.xcontact ∈ os45Figure24SourcePatch`.  This layer does not prove compact
branch equality, does not touch `extendF`, and does not use locality, PET
single-valuedness, scalar representatives, or EOW.  Therefore it may be
implemented before the OS-I branch-difference theorem.  In contrast,
`BHW.OS45CompactFigure24WickPairingEq`, and
`BHW.sourceOrientedAdjacentTubeAnchor_of_compactWickPairingEq` remain closed
until the direct OS-I §4.5 source-patch branch-difference theorem is checked.

Certified compact-patch pullback target, 2026-05-02:
`BHW.os45CompactRealPatch_pullbackSchwartz` is also proof-doc complete as a
pure finite-coordinate change of variables, and its Lean surface should be
generic in the branch integrand
`A : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ`.  For a compactly supported
Schwartz test `φ` on the `π`-real patch, set
`ψ := BHW.permuteSchwartz π.symm φ`.  Then
`ψ u = φ (os45SourcePermutationHomeomorph d n π u)` by
`permuteSchwartz_apply`; compact support is
`BHW.permuteSchwartz_hasCompactSupport`; and the support inclusion follows
from `BHW.tsupport_permuteSchwartz`, the equality between the linear
homeomorphism `x ↦ x ∘ π.symm` and `os45SourcePermutationHomeomorph d n π`,
and injectivity of that homeomorphism.  The two integral identities are
exactly `(BHW.integral_perm_eq_self π.symm h).symm`, with
`h x = A (fun k => realEmbed x (π k)) * φ x` for the left branch
and
`h x = A (fun k => realEmbed x ((π * τ) k)) * φ x` for the right
branch, plus the finite rewrites
`realEmbed (x ∘ π.symm) ∘ π = realEmbed x` and
`realEmbed (x ∘ π.symm) ∘ (π * τ) = realEmbed (x ∘ τ)`.  This theorem still
does not depend on `bvt_F` or any analytic trust boundary and does not prove
compact branch equality; it only transports an already supplied test from the
`π`-patch to the canonical source patch.  Later OS-specific consumers
specialize `A := BHW.extendF (bvt_F OS lgc n)`.

Current Lemma-2 readiness clarification, 2026-05-02: the branch-law group
`BHW.same_sourceOrientedInvariant_detOneOrbit_or_singularLimit` now has a
componentwise implementation transcript in the theorem-2 blueprint.  The
summary ledger must not describe the high-rank Witt repair, low-rank selected
block, residual-frame alignment, dual-frame construction, contraction family,
or singular two-curve limit as anonymous "proof-doc-only" gaps.  They are
still unimplemented in production Lean, but their mathematical route is pinned
to named support statements.  A future Lean pass may start inside this group
only at one of those lower support statements, for example
`BHW.extendF_complexLorentzInvariant_of_cinv`, the coefficient-kernel bridge,
the restricted-rank bridge, the determinant-repaired Witt extension support,
or the low-rank Schur/residual-frame support.  It must not start at the public
branch-law wrapper or at
`BHW.sourceOrientedScalarRepresentativeData_bvt_F`.

Current determinant/Witt refinement, 2026-05-02: the high-rank support row now
has an implementation-level finite-linear-algebra order.  Before proving the
public high-rank orbit theorem, Lean must first introduce the genuine
full-complex orthogonal group object
`BHW.HallWightmanFullComplexLorentzGroup d`, its determinant/action algebra,
the `sourceComplexMinkowskiBilinForm` bridge to Mathlib orthogonal
complements, and the Householder reflection package with determinant computed
from the decomposition `ℂ ∙ u ⊔ (ℂ ∙ u)ᗮ`.  This refinement closes a
documentation ambiguity about "choosing a sign on the complement"; it does not
close the production Lean gate for the public scalar representative or
adjacent `S'_n` wrappers.

Current oriented descent readiness clarification, 2026-05-02: the descent
group `BHW.sourceOrientedVarietyGermHolomorphicOn_extendF_descent` now has a
componentwise regular/removable transcript rather than a single amorphous
"normality" gap.  The proof-doc entry points are
`BHW.sourceOrientedQuotientValue_wellDefined`,
`BHW.sourceOrientedQuotientValue_holomorphicOn_maxRank`,
`BHW.sourceOrientedQuotientValue_continuous_locallyBounded`,
the residual-chart compact-parameter continuity and boundedness lemmas,
`BHW.sourceOrientedExceptionalRank_isAnalyticSubvariety`,
`BHW.sourceOrientedMaxRank_dense_in_domain`,
`BHW.sourceOrientedVariety_normal_riemannExtension`, and the invariant-ring
normality chain
`BHW.sourceOrientedInvariantRing_generated_by_gram_det`,
`BHW.sourceOrientedInvariantRing_relations_kernel`,
`BHW.sourceOrientedInvariantRing_integrallyClosed`, and
`BHW.sourceOrientedAlgebraicCoordinateRing_iso_invariants`.  The only
allowable external support boundary inside this chain is a standard
finite-dimensional `SO` invariant-theory theorem with explicit
pairing/volume generators and Cauchy-Binet kernel; it may not mention OS,
Wightman functions, EOW, PET, locality, or theorem 2.  The public descent
surface remains downstream of these support statements and is not the first
Lean target.

Current oriented real-uniqueness readiness clarification, 2026-05-02: the
real-patch uniqueness group
`BHW.sourceOrientedDistributionalUniquenessPatch_of_HWRealEnvironment` now has
a componentwise transcript in the theorem-2 blueprint.  The lower support
targets are `BHW.sourceOrientedLocalTotallyRealIdentity_seed`,
`BHW.sourceOrientedLocalChart_at`,
`BHW.sourceOrientedLocalChart_totallyRealSlice`,
`BHW.sourceOrientedLocalChart_shrink_to_domain_and_realPatch`,
`BHW.SourceOrientedVarietyGermHolomorphicOn.to_chart`, the
`LocalBiholomorphOnSourceOrientedVariety` inverse/differentiability fields,
the tangent package
`sourceFullFrameDetDifferential`,
`sourceOrientedDifferentialCLM`,
`sourceOrientedMinkowskiInvariant_hasFDerivAt`,
`sourceOrientedDifferential_real_complexification`, and the real subpatch
producer
`os45Figure24_realPatch_orientedRegularSubpatch`.  The determinant-regular
subpatch must be a nonempty open subpatch of the π-permuted Figure-2-4 real
patch with fixed nonzero full-frame determinant, not the old pure-Gram
`gramEnvironment`.  This producer remains a lower support target; the adjacent
seed theorem may not assume oriented distributional uniqueness before this
patch exists.

Current compact Figure-2-4 branch-difference readiness correction,
2026-05-03: the OS I Section 4.5 compact producer
`BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45` now has
a non-circular theorem surface, but production Lean must start below that
public surface.  The lower targets are
`BHW.integrable_pairings_of_os45_adjacent_euclideanEdge_on_timeSector`,
`BHW.integral_wickBranchDifference_mul_eq_zero_of_pairing_eq`,
`BHW.os45_wickBranchDifference_zero_of_euclideanEdge_pairing_eq_on_timeSector`,
`BHW.OS45SourcePatchBHWJostPairData`,
`BHW.os45_sourcePatch_bhwJostPairData_on_figure24SourcePatch_of_OSI45`,
the checked generic theorem upgrading Wick compact zero to `P.difference`
distributional zero on the selected source patch,
the real-source `extendF` integrability facts, and the
source-patch compact partition carrying `V_sourcePatch` plus
`V_orientedPath_closure`.  The old lower targets
`BHW.integral_commonBoundary_wickTrace_eq_zero_of_wickDiff_zero`,
`BHW.os45CommonBoundary_wickTrace_zero_of_compactPairing_zero`, and
`BHW.os45CommonBoundary_identity_of_wickTrace_zero` belong downstream of the
oriented branch-germ envelope; they cannot be used to prove the compact
source-patch theorem.  Production Lean has now checked the algebraic consumer
chain below the analytic producer:
`BHW.os45_pairData_difference_identity_of_wickDistributionZero`,
`BHW.os45_pairData_difference_realTrace_zero_of_wickDistributionZero`,
`BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero`,
`BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero`,
`BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero`,
and the selected-adjacent wrapper
`BHW.bvt_F_distributionalJostAnchor_of_pairData_difference_zero`.  Therefore
the next hard Lean target is not a new `DifferenceData` wrapper; it is the
direct OS-I/BHW-Jost construction of
`P : BHW.OS45SourcePatchBHWJostPairData ... V` together with Wick-side compact
zero for `P.τ` on that same `V`, using the now-checked Wick pairing
integrability support consumed by
`BHW.os45_wickBranchDifference_zero_of_euclideanEdge_pairing_eq_on_timeSector`,
plus the now-checked real-source `extendF` integrability support.  The compact
producer is a direct branch-difference theorem: checked Wick compact equality
is converted to a Wick-edge distributional zero for the OS-I branch
difference, BHW/Jost continuation carries that same difference to the selected
Figure-2-4 real source trace, and the checked pair-data algebra packages the
result.  It may not be replaced by separate real-branch `= OS.S` statements,
half-time common-edge continuity of raw `extendF`,
`BHW.os45_adjacent_commonBoundaryEnvelope`, an `AdjacentOSEOWDifferenceEnvelope`,
final locality, global PET branch independence, or local boundary-functional
demotion.

Full-frame max-rank chart refinement, 2026-05-02: the arbitrary complex chart
`BHW.sourceOrientedMaxRankChart_at` is now separated from the extended-tube
local section.  Both are produced from
`BHW.SourceOrientedFullFrameMaxRankChartData`, whose coordinates are the
selected full-frame slice parameter plus the mixed Gram rows.  The chart
inverse reconstructs the selected full frame by the full-frame gauge local
image theorem, reconstructs unselected vectors from mixed rows and the inverse
selected Gram block, and checks all determinant coordinates by oriented
relations and block determinant expansion.  The extended-tube section is then
the same chart after an extra shrink keeping the reconstructed vector map in
`BHW.ExtendedTube d n`.  Thus this subpacket now has the right proof shape,
and production Lean has started at the finite-dimensional full-frame
coordinate, tangent, and slice substrate.  The max-rank chart constructor is
still blocked until the full-frame gauge local-image theorem and
determinant-recovery algebra are implemented.

Full-frame reconstruction formula refinement, 2026-05-02: the blueprint now
spells out the actual chart inverse used by
`BHW.SourceOrientedFullFrameMaxRankChartData`.  The selected rows are the
gauge-fixed frame `M0 + X`; each unselected row is
`mixed * (sourceFullFrameGram d (M0 + X))⁻¹` expressed in that frame.  The new
pseudo-code surfaces
`BHW.sourceFullFrameGauge_reconstructVector_selected`,
`BHW.sourceFullFrameGauge_reconstructVector_mixedGram`, and
`BHW.sourceFullFrameGauge_reconstructInvariant_eq_of_frame_eq_mixedRows_eq`
make the selected/mixed-row algebra and determinant-coordinate recovery
explicit.  This
removes a chart-inverse gap, but does not close the full-frame blocker: the
full-frame local image theorem and the oriented algebraic relations still have
to be implemented before this packet is Lean-ready.

Full-frame mixed-Gram transcript refinement, 2026-05-04: the mixed-row theorem
is now pinned to the exact finite matrix cancellation used in production Lean.
Set
`M := sourceFullFrameGauge_reconstructFrame d n ι M0 slice y`,
`z := sourceFullFrameGauge_reconstructVector d n ι M0 slice y`, and
`A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of (sourceFullFrameGram d M)`.  The production hypothesis is
`hA_unit : IsUnit A.det`.  For an unselected label `k`, define
`coeff b := ∑ c, y.2 k c * A⁻¹ c b`.  The proof first rewrites
`z k.1` to `fun μ => ∑ b, coeff b * M b μ` by unfolding
`sourceFullFrameGauge_reconstructVector` with `k.2`; it rewrites
`z (ι a)` to `M a` by applying
`sourceFullFrameGauge_reconstructVector_selected`.  Expanding
`sourceComplexMinkowskiInner` and `sourceFullFrameGram` then gives
`sourceComplexMinkowskiInner d (fun μ => ∑ b, coeff b * M b μ) (M a)
 = ∑ b, coeff b * A b a`.  The final equality is obtained from
`Matrix.nonsing_inv_mul_cancel_right (A := A) row hA_unit`, where
`row : Matrix (Fin 1) (Fin (d + 1)) ℂ := fun _ b => y.2 k b`; evaluating the
matrix equality at `(0 : Fin 1), a` reduces by `Matrix.mul_apply` to
`∑ b, coeff b * A b a = y.2 k a`.  Thus the remaining Lean work for this lemma
is finite-sum normalization only, not a new mathematical argument.

Full-frame coefficient-row determinant refinement, 2026-05-04: determinant
recovery is factored through a generic reconstruction algebra packet before
the oriented Schur relations are used.  Define
`sourceFullFrameGauge_reconstructCoeff d n ι M0 slice y j b` to be the identity
row when `j = ι a`, and the mixed row
`∑ c, y.2 k c * A⁻¹ c b` when `j` is unselected, with
`A = Matrix.of (sourceFullFrameGram d reconstructedFrame)`.  The Lean target
`sourceFullFrameGauge_reconstructVector_eq_sum_coeff_frame` proves, by cases
on `j ∈ Set.range ι`, that every reconstructed vector is
`∑ b, coeff j b • reconstructedFrame b`.  Consequently, for every embedding
`κ`, `sourceFullFrameMatrix d n κ reconstructedVector =
  (fun a b => coeff (κ a) b) * reconstructedFrame`, and
`sourceFullFrameDet d n κ reconstructedVector =
  det(fun a b => coeff (κ a) b) * reconstructedFrame.det`.  This is the exact
finite-dimensional determinant spine needed by the later oriented relation
`det coeff * G.det ι = G.det κ`; no determinant-coordinate field may be assumed
or stored as unexplained data.  The same coefficient packet also includes the
Gram expansion
`sourceComplexMinkowskiInner d z_i z_j =
 ∑ a, ∑ b, coeff i a * coeff j b *
   Matrix.of (sourceFullFrameGram d reconstructedFrame) a b`, proved only from
bilinearity of `sourceComplexMinkowskiInner`.  This separates pure
reconstruction algebra from the later Schur theorem that identifies the
coefficient Gram expression with the input oriented source Gram data.
Input-side coefficient packet refinement, 2026-05-04: the oriented recovery
side now has the matching Lean surfaces:
`sourceSelectedFrameGramMatrix d n ι G`,
`sourceSelectedFrameCoeff d n ι G j b`, and
`sourceCoeffGramFromSelected d n ι G i j`; the checked helper names are
`sourceSelectedFrameGramMatrix_apply`, `sourceSelectedFrameCoeff_selected`, and
`sourceCoeffGramFromSelected_selectedSelected`.  With an invertible selected
Gram block, `sourceCoeffGramFromSelected_unselectedSelected` also recovers the
unselected-selected mixed entries by the same matrix cancellation
`row * A⁻¹ * A = row`.  The hypothesis needed by this cancellation is now
bridged by
`sourceSelectedFrameGramMatrix_det_isUnit_of_variety_det_ne_zero`, which proves
that `G ∈ sourceOrientedGramVariety d n` and `G.det ι ≠ 0` make the selected
Gram block invertible.  The symmetry helpers
`sourceOrientedGramVariety_gram_symm` and
`sourceSelectedFrameGramMatrix_symm_of_variety` are checked as well, and
`sourceCoeffGramFromSelected_symm_of_selectedGram_symm` plus
`sourceCoeffGramFromSelected_selectedUnselected_of_variety` close the
selected-unselected mixed orientation.  Selected labels have identity
coefficient rows, so the hard theorem is now honestly localized: prove the
remaining unselected-unselected source Gram entries from the Schur complement;
then use the coefficient determinant factorization plus the oriented determinant
relation to recover all determinant coordinates.
The Schur-complement proof is further split by the conditional theorem
`sourceCoeffGramFromSelected_eq_gram_of_invariant_vector_expansion`: if a
realizing tuple `z` for `G` satisfies
`z j = ∑ a, sourceSelectedFrameCoeff d n ι G j a • sourceFullFrameMatrix d n ι z a`
for every source label `j`, then
`G.gram i j = sourceCoeffGramFromSelected d n ι G i j` for all `i,j`.  Thus the
remaining hard Gram theorem is exactly the selected full-frame vector-expansion
theorem under `G.det ι ≠ 0`, not any additional coordinate algebra.
The vector-expansion proof is Lean-ready as follows.  First prove
`sourceFullFrameMatrix_rows_span_top_of_det_ne_zero`: nonzero determinant of
`M := sourceFullFrameMatrix d n ι z` gives
`LinearIndependent ℂ (fun a => M a)` by
`Matrix.linearIndependent_rows_of_det_ne_zero`, and the card/finrank equality
for `Fin (d + 1) -> ℂ` upgrades this to
`Submodule.span ℂ (Set.range (fun a => M a)) = ⊤`.  For an unselected label
`j`, set `k := ⟨j,hj⟩`, `A := sourceSelectedFrameGramMatrix d n ι G`, and
`row _ a := G.gram j (ι a)`.  The coefficient row is exactly `row * A⁻¹`.
For each selected row `b`, `Matrix.nonsing_inv_mul_cancel_right (A := A) row`
proves that the Minkowski pairing of
`z j - ∑ a, sourceSelectedFrameCoeff d n ι G j a • M a` with `M b` is zero.
Since the `M b` span and `sourceComplexMinkowskiInner` is nondegenerate on the
left, `sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family`
forces the difference to vanish.  The selected-label case is the identity-row
sum.
Lean implementation checkpoint, 2026-05-04:
`sourceFullFrameMatrix_rows_span_top_of_det_ne_zero`,
`sourceSelectedFrameCoeff_vector_expansion_of_invariant`, and
`sourceOrientedVariety_schurGram_eq_of_selectedDet_ne_zero` are checked.  The
unselected-unselected Schur Gram blocker is therefore closed in production
Lean.  Determinant recovery now follows the same expansion route: for any
embedding `κ`, the selected full-frame matrix `sourceFullFrameMatrix d n κ z`
is the coefficient matrix
`Matrix.of (fun a b => sourceSelectedFrameCoeff d n ι G (κ a) b)` times the
base selected frame `sourceFullFrameMatrix d n ι z`; applying
`Matrix.det_mul` proves
`det coeff * G.det ι = G.det κ`.
Lean implementation checkpoint, 2026-05-04:
`sourceSelectedFrameCoeff_matrix_eq_frame_of_invariant` and
`sourceOrientedVariety_det_eq_coeff_det_selected` are checked.  The next chart
inverse bridge is now purely computational: if the reconstructed frame equals
`sourceFullFrameMatrix d n ι z` and the free mixed rows equal
`sourceSelectedMixedRows d n ι (sourceOrientedMinkowskiInvariant d n z)`, then
`sourceFullFrameGauge_reconstructVector d n ι M0 S y = z`.  The selected labels
use `sourceFullFrameGauge_reconstructVector_selected`; unselected labels use
the same inverse-Gram coefficient row as
`sourceSelectedFrameCoeff_vector_expansion_of_invariant`.
Lean implementation checkpoint, 2026-05-04:
`sourceFullFrameGauge_reconstructVector_eq_of_frame_eq_mixedRows_eq` and
`sourceFullFrameGauge_reconstructInvariant_eq_of_frame_eq_mixedRows_eq` are
checked.  The explicit reconstruction inverse is now algebraically complete:
once the full-frame local-image step supplies the selected frame and the chart
uses the source mixed rows, the reconstructed oriented invariant is exactly the
input invariant.
Max-rank chart API checkpoint, 2026-05-04:
`sourceComplementIndex_fintype`, `sourceFullFrameMaxRankChartModel`,
`sourceFullFrameGauge_reconstructInvariant`,
`sourceFullFrameGauge_reconstructInvariant_mem_variety`,
`sourceFullFrameOrientedCoordOfSource_reconstructInvariant_eq`,
`sourceSelectedFrameGramMatrix_reconstructInvariant_eq`,
`sourceFullFrameGauge_reconstructInvariant_selectedDet`,
`sourceSelectedFrameGramMatrix_reconstructInvariant_det_isUnit`,
`sourceSelectedMixedRows_reconstructInvariant_eq`,
`sourceSelectedMixedRows_reconstructInvariant_eq_of_frame_det_ne_zero`,
`SourceOrientedFullFrameMaxRankChartData`, and
`SourceOrientedFullFrameMaxRankChartData.to_maxRankChart` are checked.  The
production packet uses the already existing selected coordinate
`sourceFullFrameOrientedCoordOfSource`; it has no obsolete `hn` or
`[NeZero d]` parameters in the reconstruction layer.  Its model is exactly
`slice.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)`, its inverse field
is forced by the explicit reconstructed source invariant, and its forgetful
map feeds the existing `SourceOrientedMaxRankChartData` API.  The right-inverse
algebra has also been split into checked selected-coordinate and mixed-row
readoff facts: the reconstructed invariant is in the source variety, its
selected full-frame coordinate is
`sourceFullFrameOrientedGramCoord d (sourceFullFrameGauge_reconstructFrame ...)`,
its selected Gram matrix and determinant are exactly those of the reconstructed
selected frame, and, under the selected Gram invertibility hypothesis, its
mixed rows are exactly the free `y.2`.  The determinant-nonzero version is also
checked, so the right-inverse mixed-row proof can consume the source-side
determinant shrink directly.  The remaining constructor work is therefore not
packet design: it is the local-image/domain construction proving the selected
coordinate lies in the kernel-chart target, the chart image is the shrunken
`kernelChart.source ×ˢ Set.univ`, and the explicit reconstruction inverse
gives both left and right inverses on that product.
Max-rank chart inverse refinement, 2026-05-04:
`sourceFullFrameSymmetricEquation_implicitChart_fst`,
`sourceFullFrameSymmetricEquation_implicitChart_eq_zero_kernelProjection`,
`sourceFullFrameSelectedImplicitChart_eq_zero_kernelCoord`,
`sourceFullFrameGaugeSliceMapSymmetric_implicitChart_eq_zero_kernelMap`,
`sourceFullFrameSelectedSymmetricCoordOfSource_eq_gaugeSliceMapSymmetric_of_kernel_eq`,
`sourceFullFrameOrientedCoordOfSource_eq_gaugeSliceMap_of_kernel_eq`,
`sourceFullFrameGauge_reconstructInvariant_selectedCoord_eq_of_kernel_eq`,
`sourceSelectedFrameCoeff_eq_of_selectedCoord_eq_mixedRows_eq`,
`sourceCoeffGramFromSelected_eq_of_selectedCoord_eq_mixedRows_eq`,
`sourceOrientedGramData_eq_of_selectedCoord_eq_mixedRows_eq`,
`sourceFullFrameGauge_reconstructInvariant_eq_of_selectedCoord_eq_mixedRows_eq`,
and `sourceFullFrameGauge_reconstructInvariant_eq_of_kernel_eq_mixedRows_eq`
are checked.  The selected-frame equality formerly demanded from the future
local-image theorem is no longer the right boundary.  The local-product chart
only has to prove that, after the source/target shrink, (i) the selected
source coordinate and the gauge-slice coordinate are both in the symmetric
implicit-chart source, (ii) their kernel coordinates agree, and (iii) the free
mixed coordinate is `sourceSelectedMixedRows d n ι G`.  The invariant equality
then follows by the checked theorem
`sourceFullFrameGauge_reconstructInvariant_eq_of_kernel_eq_mixedRows_eq`.
Thus the remaining local-image theorem is now a topology/domain theorem plus
the definitional mixed-row readoff, not another Schur-block algebra theorem.
Lean implementation checkpoint, 2026-05-04:
`SourceOrientedFullFrameMaxRankChartData` now records the selected
determinant-nonzero shrink as `Ω_selectedDetNonzero`, and exposes
`mem_variety_of_mem_Ω`, `mem_Ωamb_of_mem_Ω`,
`selectedDet_ne_zero_of_mem_Ω`, `kernelChart_apply_eq`,
`kernelChart_right_inv_implicitKernel`,
`kernelChart_left_inv_implicitKernel`,
`sourceFullFrameSymmetrizeCoord`,
`continuous_sourceFullFrameSymmetrizeCoord`,
`sourceFullFrameSelectedSymmetricCoordAmbient`,
`continuous_sourceFullFrameSelectedSymmetricCoordAmbient`,
`sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety`,
`sourceFullFrameSelectedKernelCoordAmbient`,
`sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety`,
`SourceOrientedFullFrameMaxRankChartData.chartCandidate`,
`SourceOrientedFullFrameMaxRankChartData.chart_eq_chartCandidate`,
`reconstructInvariant_eq_of_selectedKernel_target_mixedRows`,
`reconstructInvariant_eq_of_mem_Ω_selectedKernel_target_mixedRows`,
`reconstructInvariant_chartCandidate_eq_of_mem_Ω`,
`reconstructInvariant_chartCandidate_eq_of_mem_Ω_from_fields`, and
`reconstructInvariant_chart_eq_of_mem_Ω_from_fields`.  The packet now also
stores the three shrink facts
`Ω_selectedSymmetric_mem_implicitSource`,
`Ω_selectedKernel_mem_target`, and
`Ω_gaugeSlice_mem_implicitSource`, plus the formula equality
`chart_eq_candidate`.  The actual stored-chart left inverse is therefore a
checked theorem: from `G ∈ C.Ω`,
`sourceFullFrameGauge_reconstructInvariant d n ι C.M0 C.slice (C.chart G) = G`.
The determinant and source-variety hypotheses are read from the packet instead
of being re-proved at each downstream use, and the total ambient chart formula
uses the symmetrized selected coordinate so it is defined before restricting
to the source variety.
Lean implementation checkpoint, 2026-05-04:
the constructor shrink has now been started in checked Lean.  The symmetric
implicit chart exposes `sourceFullFrameSymmetricBase_mem_implicitChart_source`
and `sourceFullFrameSymmetricEquation_implicitChart_source_mem_nhds_base`.
The selected ambient coordinate layer proves
`sourceFullFrameSelectedSymmetricCoordAmbient_eq_base_of_oriented_eq`,
`sourceFullFrameSelectedSymmetricCoordAmbient_mem_implicitSource_at_base`,
`sourceFullFrameSelectedSymmetricCoordAmbient_eventually_mem_implicitSource`,
`sourceFullFrameSelectedKernelCoordAmbient_eq_zero_at_base`,
`continuousAt_sourceFullFrameSelectedKernelCoordAmbient_at_base`,
`sourceFullFrameSelectedKernelCoordAmbient_eventually_mem_kernelTarget`, and
`sourceFullFrameSelectedKernelCoordAmbient_eventually_gaugeSlice_mem_implicitSource`.
The pure kernel-chart lift proves
`sourceFullFrameGaugeSliceImplicitKernel_symm_implicitSource_mem_nhds_zero`.
These are combined in the checked structure/constructor
`SourceFullFrameMaxRankChartAmbientShrink` and
`sourceFullFrameMaxRankChart_ambientShrink`, which produces an open ambient
neighborhood of the base point where all three source/target membership facts
and `G.det ι ≠ 0` hold.  The shrink now also exposes
`SourceFullFrameMaxRankChartAmbientShrink.relDomain`,
`relDomain_relOpen`, `center_mem_relDomain`, `chartCandidate`,
`chartCandidate_fst`, `chartCandidate_snd`,
`selectedKernelCoordAmbient_continuousOn_Ωamb`,
`chartCandidate_continuousOn_Ωamb`,
`chartCandidate_continuousOn_relDomain`,
`sourceOrientedMaxRankAt_of_selectedDet_ne_zero`,
`maxRank_of_mem_relDomain`, and the constructor-level left inverse
`reconstructInvariant_chartCandidate_eq_of_mem_relDomain`.  The model-side
right inverse is also checked as
`sourceFullFrameSelectedKernelCoord_reconstructInvariant_eq`,
`sourceFullFrameSelectedKernelCoordAmbient_reconstructInvariant_eq`, and
`chartCandidate_reconstructInvariant_eq_of_chartSource_frameDet`.  Finally,
`localBiholomorph`, `exists_restrict_modelOpen_image_eq`,
`toFullFrameMaxRankChartData`, and
`toFullFrameMaxRankChartData_of_modelOpen` are checked.  Thus the next
constructor task is no longer to re-prove kernel/mixed-row algebra or chart
packet assembly.  It is to produce an open model set `V` around the center
such that reconstructed points of `V` stay in the previous relative domain,
have slice coordinate in `kernelChart.source`, have nonzero reconstructed
selected determinant, and the explicit reconstruction map is differentiable
and continuous on `V`.  The checked `toFullFrameMaxRankChartData_of_modelOpen`
then builds `SourceOrientedFullFrameMaxRankChartData`.
Model-open constructor transcript, 2026-05-04: the remaining `V` is not an
extra geometric choice.  For an ambient shrink
`T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0`, take
`V = {y | y.1 ∈ kernelChart.source}
  ∩ ((sourceFullFrameGauge_reconstructInvariant d n ι M0 S) ⁻¹' T.Ωamb
      ∩ sourceFullFrameGaugeModelDetNonzero d n ι M0 S)`.
The three membership projections are then immediate.  Openness is the
intersection of the kernel-chart source preimage, the determinant-nonzero model
locus, and the `continuousOn_iff'` preimage of `T.Ωamb` under the explicit
reconstruction, restricted to the determinant-nonzero locus.  The reconstruction
regularity input is now finite-dimensional calculus only:
`sourceFullFrameGauge_reconstructFrame` is differentiable; on
`sourceFullFrameGaugeModelDetNonzero`, `sourceFullFrameGauge_reconstructVector`
is differentiable because every coordinate is a finite sum of entries of
`(Matrix.of (sourceFullFrameGram d reconstructedFrame))⁻¹`, and matrix inverse
is `det⁻¹ • adjugate` on the determinant-unit locus; composing with
`sourceOrientedMinkowskiInvariant` gives differentiability and continuity of
`sourceFullFrameGauge_reconstructInvariant`.  At the center, the selected kernel
coordinate is zero, the inverse kernel chart sends zero to zero by its checked
left-inverse theorem, hence the reconstructed selected frame is exactly `M0`;
the determinant condition is `hM0.ne_zero`, and reconstruction belongs to
`T.Ωamb` because the checked left inverse gives back `G0 ∈ T.relDomain`.  This
is a mechanical Lean target and should be implemented as the model-domain
constructor feeding `toFullFrameMaxRankChartData_of_modelOpen`, with no new
axioms or sorrys.
Lean implementation checkpoint, 2026-05-06: the model-domain constructor is
now checked as `toFullFrameMaxRankChartData_of_modelChartDomain`, and the
source-based constructor
`sourceOrientedFullFrameMaxRankChartData_at_source` builds the full-frame chart
from the actual realizing tuple `z0` instead of an arbitrary variety witness.
Its checked center theorem
`sourceOrientedFullFrameMaxRankChartData_at_source_reconstructVector_center`
proves that the explicit reconstructed source tuple at
`sourceOrientedMinkowskiInvariant d n z0` is exactly `z0`.  The remaining
full-frame max-rank local-section work is therefore twofold: first prove the
ambient differentiability theorem for the chart-candidate section, i.e. the
implicit-kernel inverse regularity behind
`SourceFullFrameMaxRankChartAmbientShrink.chartCandidate`; then use continuity
on the ambient chart/model-det-nonzero domain and
`isOpen_extendedTube.mem_nhds hz0` to obtain an ambient open set on which
`sourceFullFrameGauge_reconstructVector d n ι C.M0 C.slice (C.chart G)` stays
inside `ExtendedTube d n`.

Ambient-domain split refinement, 2026-05-02: the full-frame max-rank chart now
stores both the relative variety chart domain `C.Ω` and an ambient open
neighborhood `C.Ωamb`, with
`C.Ω = C.Ωamb ∩ sourceOrientedGramVariety d n`.  The tube-valued section uses
`C.Ωamb`, not the relative domain, and the blueprint now names the continuity
shrink packet
`BHW.SourceFullFrameMaxRankChartAmbientShrink.tubeShrink_at_source`.  Its proof
uses the source-based center theorem to identify the reconstructed center with
the original extended-tube source tuple exactly, then shrinks the ambient
neighborhood inside the open extended tube.  This fixes an implementation-level
topology gap in the previous transcript, while leaving the implicit-inverse
differentiability theorem as the real full-frame holomorphic-section blocker.

Full-frame chart constructor refinement, 2026-05-02: the constructor
`BHW.sourceOrientedFullFrameMaxRankChartData_at` is now expanded into an
implementation transcript.  It starts from a realizing tuple for
`G0 ∈ sourceOrientedGramVariety`, selects `M0 := sourceFullFrameMatrix ι z0`,
uses `G0.det ι ≠ 0` to obtain an invertible frame, calls the checked
`sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph`, shrinks its
source/target to the determinant-nonzero sheet after transport through the
symmetric implicit chart, sets `Ω = Ωamb ∩ sourceOrientedGramVariety`, and
defines the chart as
`(kernelChart.symm selectedKernelCoord, sourceSelectedMixedRows)`.  The chart
image is proved to be `kernelChart.source ×ˢ univ` after the explicit shrink;
the inverse is the explicit reconstructed source invariant.  This closes the
constructor-shape gap, but the transcript still depends on the hypersurface
transport/local-image theorem and determinant recovery subtheorems listed in
the blueprint.

Full-frame determinant-recovery refinement, 2026-05-02: the reconstruction
proof no longer hides the phrase "block determinant expansion."  The blueprint
now names the coefficient-row map `BHW.sourceSelectedFrameCoeff`, the Schur
Gram theorem
`BHW.sourceOrientedVariety_schurGram_eq_of_selectedDet_ne_zero`, the
sign-sensitive determinant theorem
`BHW.sourceOrientedVariety_det_eq_coeff_det_selected`, and the two recovery
theorems
`BHW.sourceFullFrameGauge_reconstructVector_gram_eq` and
`BHW.sourceFullFrameGauge_reconstructVector_det_eq`.  The determinant proof is
fixed by the identity
`det(G[κ,ι]) = minkowskiMetricDet d * G.det κ * G.det ι`, the expansion
`G[κ,ι] = Cκ * A`, and
`det A = minkowskiMetricDet d * (G.det ι)^2`, so the selected determinant
coordinate, not a square-root choice, fixes the special-orthogonal sheet.  The
Schur proof is now pinned through
`BHW.sourceSelectedFrameCoeff_vector_expansion`, reducing it to the ordinary
finite-dimensional statement that a nonzero selected full-frame determinant
makes the selected source vectors a basis and the Gram-inverse coefficient row
recovers each source vector.

Full-frame local-image refinement, 2026-05-02: the blueprint now expands the
finite-dimensional local-image theorem behind the selected-frame gauge.  It
records the actual derivative of
`sourceFullFrameOrientedEquation d`,
`Y ↦ det(H0.1) * trace(H0.1⁻¹ * Y.1)
   - 2 * minkowskiMetricDet d * H0.2 * Y.2`, proves regularity in the
determinant-coordinate direction, and corrects the target from an ambient
zero-locus slogan to a regular zero locus inside the symmetric Gram-coordinate
submodule.  The kernel calculation is pinned by `B := M0⁻¹ * X`, giving
`B * η + η * Bᵀ = 0` and `trace B = 0`, hence the infinitesimal
determinant-`1` Lorentz orbit.  The range calculation is pinned by
rank-nullity and the explicit dimensions `D^2`, `D(D-1)/2`, and `D(D+1)/2`.
The remaining work is now finite-dimensional Lean infrastructure for those
matrix derivative, finrank, and local-implicit-image statements; this is still
proof-doc-only and does not open production Lean.

Full-frame local-image proof-body refinement, 2026-05-02: the blueprint now
adds the proof bodies that the previous refinement only named.  The derivative
packet is split through Jacobi's determinant formula
`matrix_det_hasFDerivAt_trace`, the bilinear derivative of
`M ↦ M * η * Mᵀ`, the determinant derivative of `M.det`, and their product as
`sourceFullFrameOrientedGram_hasFDerivAt`.  Regularity now proves the
determinant-coordinate direction is nonzero and packages the symmetric
determinant direction explicitly.  The hypersurface local-image theorem now
calls the finite-dimensional regular-zero-locus slice theorem with the actual
slice derivative range and kernel, while the variety local-image theorem is
only a restriction of the hypersurface inverse using
`sourceFullFrameOrientedGramVarietyCoord_subset_hypersurface`.  This removes
the previous named-but-unassembled local-image proof gap.  The packet remains
proof-doc-only because the standard finite-dimensional support still has to be
moved into Lean without new axioms or production sorrys.

Full-frame slice/rank refinement, 2026-05-02: the selected-frame gauge slice
packet is no longer just a complement slogan.  The blueprint now constructs
`SourceFullFrameGaugeSliceData` by choosing a complement to the orbit tangent
kernel, restricting `sourceFullFrameOrientedDifferentialCLM` to that
complement, proving injectivity from `S ⊓ kernel = ⊥`, and proving
surjectivity by decomposing any preimage as a slice vector plus a kernel
vector.  The downstream theorem
`sourceFullFrameSlice_restricted_range_eq_tangent` is now proved from the
stored linear equivalence rather than from an unpinned complement API call.
The rank proof is also corrected: the symmetric-plus-determinant coordinate
submodule has dimension `D(D+1)/2 + 1`, the oriented equation has a nonzero
determinant-coordinate derivative, and the tangent kernel therefore has
dimension `D(D+1)/2`.  The proof-body transcript names the trace identity for
the Gram differential, the kernel component equalities, the skew-matrix
linear equivalence for the special Lorentz Lie algebra, and the finite
rank-nullity/arithmetic helpers.  The standard helper surfaces
`skewMatrixSubmodule_finrank`, `specialLorentzLieAlgebra_skewLinearEquiv`,
`sourceSymmetricMatrix_withDet_factorization_finrank`,
`matrix_inv_mul_three_of_isUnit`, and
`sourceFullFrameOrientedTangentSpace_linearEquiv_kernel` are now explicit
rather than implicit.  This closes a real finite-dimensional documentation
gap, but production Lean for the packet is not started until those standard
linear-algebra helper surfaces are implemented sorry-free in Lean.

Paper-source fork audit.  Hall-Wightman Theorem I proves scalar-product
dependence from the real orthochronous Lorentz invariance hypotheses, and its
Lemma 1 discusses the extension through the space-inversion/improper component
when constructing the single-valued continuation.  OS I Section 4.5, however,
uses the Bargmann-Hall-Wightman theorem to obtain the proper-complex
`L_+(C)` continuation required for locality.  The strict OS implementation
therefore cannot identify equal ordinary source Gram matrices in the full
scalar-rank case unless it also has the full-component Hall-Wightman source
input.  The active route avoids that unsourced import by using the oriented
source invariant: the ordinary Gram coordinates plus all ordered full-frame
determinants.  Equality of these oriented data is exactly what converts the
full-rank determinant ratio to `1`, while lower-rank fibres still go through
the Hall-Wightman singular contraction theorem.  Consequently,
`BHW.sourceScalarRepresentativeData_bvt_F` stays a conditional ordinary fork,
and the production-bound target is
`BHW.sourceOrientedScalarRepresentativeData_bvt_F` with its oriented adjacent
`S'_n` consumers.

1. `BHW.extendedTube_same_sourceGram_extendF_eq`: the same-source-Gram branch
   law must prove both the high scalar-rank complex Lorentz orbit case and the
   low-rank Hall-Wightman singular contraction/continuity case.  The rank
   split is `min d n <= sourceGramMatrixRank` versus `< min d n`; it is not
   `SourceComplexGramRegularAt`.  The high-rank quotient-span fields are now
   written as Lean-shaped proofs: source generators enter the quotient ranges
   by `Pi.single`, preservation of the restricted Minkowski form is the finite
   coefficient expansion against the common source Gram matrix, and Witt
   extension then maps every source vector in the determinant-compatible
   cases.  A new orientation gate is now explicit: proper
   `ComplexLorentzGroup d` invariance alone cannot prove full scalar-product
   descent in scalar rank `d + 1`, because the determinant/pseudoscalar of a
   full source frame is invariant under determinant-`1` Lorentz maps and
   changes under an improper same-Gram frame.  The branch law therefore also
   needs Hall-Wightman's improper/space-inversion component input, recorded as
   `BHW.hallWightman_improperComponentInvariant_forwardTube` and
   `BHW.hallWightmanFullComplexLorentzInvariantOnExtendedTube_eq`, or an
   already implemented sorry-free full-complex-orthogonal Hall-Wightman source
   theorem with the same content.  The low-rank normal-form-to-data
   step is also explicit: the orbit witnesses are exactly
   `N.contract t * N.Λ0` on the left and `N.contract t` on the right, with the
   finite coordinate proof using `N.left_eq`, `N.right_eq`,
   `N.contract_fix_ξ`, `N.contract_scale_q`, and
   `BHW.complexLorentzAction_mul`.  Remaining work in this blocker is the
   finite-dimensional Hall-Wightman geometry producing the selected span,
   residual isotropic frame, dual frame, and contraction family; it is not an
   analytic-continuation or locality argument.
2. `BHW.sourceExtendedTubeGramDomain_relOpen`: Hall-Wightman Lemma 3 must
   produce local vector realizations inside the ordinary extended tube for
   nearby scalar-variety points, including singular rank.  The connectedness
   half is mechanical, but relative openness is not a continuous-image
   theorem.  The open-neighborhood wrapper has now been reduced to two
   concrete pieces: a finite Pi-coordinate ball shrink from an arbitrary
   source neighborhood, and the Hall-Wightman adapted-base quantitative
   perturbation theorem.  The arbitrary representative is first replaced by
   the same-Gram adapted representative obtained by selected-span projection
   and residual isotropic-frame deletion; this reuse of
   `hw_isotropicFrame_allCoefficients_mem_extendedTube` is the singular-rank
   content and must be proved before Lean consumes the relative-open theorem.
3. `BHW.sourceVarietyGermHolomorphicOn_extendF_descent`: the scalar value
   function must be the branch-defined `Phi`, and the proof must give
   `SourceVarietyGermHolomorphicOn` charts on the source Gram analytic
   variety.  Equality of ambient representatives off the variety is not
   allowed.
4. The Hall-Wightman Lemmas 4--7 chart package must be complete:
   max-rank power-series scalar charts, invariant PDE/auxiliary-coordinate
   independence, continuity and local boundedness of the branch-defined
   scalar value, and removable singularity across the exceptional
   determinantal locus.
5. The normal analytic-space support must be real SCV/algebraic geometry:
   `sourceComplexGramVariety_normal`,
   `sourceComplexGramVariety_relOpen_subset_closure_inter_maxRank`,
   `sourceGramVariety_normal_riemannExtension`, and the symmetric
   determinantal Serre/CM/R1 subpacket.  These may be proved locally or
   imported from sorry-free support, but may not be replaced by vacuous
   predicates, axioms, or theorem-2-specific wrappers.
6. The OS I §4.5 canonical compact producer
   `BHW.os45CanonicalAdjacentBranchBoundaryData_of_OSI45` must be proved from
   equations (4.1), (4.12), (4.14), compact zero-diagonal Euclidean symmetry,
   BHW continuation, and Jost/Ruelle real-environment uniqueness.  The generic
   `BHW.JostRuelleCompactBoundaryData` theorem is OS-free; the OS-specific
   producer is still genuine source mathematics, not a forwarding wrapper.
   Its proof is now required to expose four internal packets: connected
   Figure-2-4 Jost/Ruelle domain and lift membership, ordinary `extendF`
   branch holomorphy/invariance from `bvt_F`, adjacent OS-I branch production
   from (4.1)/(4.12)/(4.14), and the compact real Jost boundary comparison
   using the exact `φZ`/`ψZ` orientation with one `OS.E3_symmetric` call.  The
   final carrier fields `jr_lift_eq`, `ordinary_eq_extendF_on_lift`, and
   `adjacent_lift_pairing_eq_permutedSchwinger` must be assembled from those
   packets, not from scalar representatives or downstream source equality.

No approved theorem-specific source-import boundary exists for these blockers.
Standard finite-dimensional support theorems named above may be proved in
local support files or consumed only if they are already sorry-free with the
same statement.  If a future session proposes a new source boundary, it must
be proposition-valued, exact in parameters and conclusions, contain no
OS/EOW/PET/locality/bvt_W language except where the OS I §4.5 compact
producer necessarily mentions OS data, and be explicitly approved before any
production Lean consumes it.

Local code audit after checkpoint `c789249` (2026-05-01): the supporting
germ API is present, but the scalar-source producers are not.  The production
tree defines `BHW.SourceVarietyGermHolomorphicOn`,
`BHW.SourceScalarRepresentativeData` with
`Phi_holomorphic : SourceVarietyGermHolomorphicOn`, and the downstream
source-variety identity support
`BHW.sourceComplexGramVariety_identity_principle`,
`BHW.SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram`, and
`BHW.SourceVarietyGermHolomorphicOn.comp_differentiableOn_chart`.  A local
search of `OSReconstruction/` still finds no production declaration named
`BHW.extendedTube_same_sourceGram_extendF_eq`,
`BHW.sourceExtendedTubeGramDomain_relOpen_connected`,
`BHW.sourceVarietyGermHolomorphicOn_extendF_descent`,
`BHW.sourceScalarRepresentativeData_of_branchLaw`,
`BHW.hallWightman_sourceScalarRepresentativeData`, or
`BHW.sourceScalarRepresentativeData_bvt_F`.  It also finds no production
declarations for the adjacent compact-source gates
`BHW.os45CanonicalAdjacentBranchBoundaryData_of_OSI45`,
`BHW.jostRuelle_uniqueContinuation_compactBoundary`,
`BHW.os45AdjacentSPrimeScalarizationChart_of_figure24`,
`BHW.os45AdjacentSPrimeSourceEq_of_compactWickPairingEq`,
`BHW.os45AdjacentSPrimeScalarSeed_of_compactWickPairingEq`, or
`BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq`.  Therefore
the available Lean support may be cited in proof docs, but it does not make
the active scalar representative (or the conditional ordinary fork) or the
adjacent `S'_n` seed package implementation-ready.

Pseudo-code audit update (2026-05-01): the active scalar-source and adjacent
`S'_n` transcripts no longer leave anonymous proof holes in the mechanical
assembly layers.  The branch-law quotient-span fields, low-rank orbit fields,
Lemma-3 finite topology wrappers, max-rank dual-coordinate/fiber-product
support, branch-defined continuity/local boundedness, and canonical compact
integral rewrites are written with explicit Lean-shaped `by` blocks.  The
max-rank kernel theorem is also now decomposed at proof-doc level: choose the
selected-row datum, read the selected compatibility equations from
`D(sourceMinkowskiGram) X = 0`, apply the infinitesimal Witt-extension theorem,
and then split into the cases `d + 1 <= n` and `n <= d + 1`.  In the first
case, selected rows span the ambient Minkowski space and the row-relation
transfer lemma forces every unselected velocity row; in the second, the
selected index map is surjective.  The reverse inclusion is the explicit
skew-generator expansion showing
`sourceGramDifferential_lorentzInfinitesimalTangent_zero`.  This does not make
the route production-Lean-ready: the remaining blockers are the named
mathematical producers above, especially the finite-dimensional
Hall-Wightman geometry, the normal/removable analytic-space packet, and the
OS I §4.5 canonical compact producer.  Remaining schematic holes elsewhere in
`theorem2_locality_blueprint.md` are archived optional bridges or downstream
post-source-route sketches; they are not permission to start Lean on
`BHW.sourceScalarRepresentativeData_bvt_F`.

Current local Slot 1 correction: the OS45 common-chart/EOW supplier is no
longer the equal-time/post-radius plan.  The checked SCV input is
`SCV.chartDistributionalEOW_local_envelope`; the OS45 proof must instantiate
it at an ordered identity-sector horizontal edge.  The common-boundary
dependency shape is fixed,
and the branch CLM theorem slots are now exposed: the adjacent branch is the
ordinary OS-II branch for the relabelled patch `x ∘ τ`, transported back by
the OS45 reindexing identity.  The one-branch OS-II/BHW horizontal boundary
theorem is now decomposed into named source, common-germ, and branch-BV
theorems; the
compact-direction `hlocal` domain hypotheses are reduced to the documented
openness/compactness lemma once the source patch supplies closure-level edge
membership.
The bounded identity perturbation and same-patch identity geometry are
checked.  The proposed horizontal-edge forward-tube pair
and pointwise equality `Hplus = Hminus` from two applications of
`BHW.extendF_eq_on_forwardTube` are rejected: after the repo permutation action
`permAct σ z = fun k => z (σ k)`, an adjacent swap reverses the relevant
horizontal time-imaginary gap.  The replacement is a branchwise horizontal
ACR/BHW common-boundary packet: construct the identity and swapped branch
horizontal-edge CLMs `Tid` and `Tτ`, prove ACR-side and BHW-side uniform
compact-direction boundary values for each branch, subtract to get the
`hplus_bv`/`hminus_bv` input with `Tdiff = Tτ - Tid`, and only then call the
one-chart theorem.  `Tdiff` is not assumed zero and is not the final real-edge
locality distribution.  The branchwise packet is local and non-circular:
`Tid` and `Tτ` are full CLMs produced by the OS45 branchwise distributional
boundary-value theorem, on the selected ordered quarter-turn edge and the
relabelled ordered patch `x ∘ τ` respectively;
`BHW.os45QuarterTurnConfig_reindexed_realBranch_eq` then places both branches
at the same quarter-turn chart point.  The zero-diagonal Schwinger functional
and `OS.E3_symmetric` verify the compact Jost-supported Euclidean restriction
of those CLMs; they cannot by themselves define the full CLMs needed by SCV.
Nor should these CLMs be treated as direct pullbacks of the final physical
real-time distribution `bvt_W`, since the OS45 horizontal edge is real only in
the quarter-turn chart.
The later Hall-Wightman source theorem consumes the resulting compact-test
anchor and must not be used to construct it.  The global compact-direction
`bvt_W` boundary transport remains useful elsewhere.
The latest proof-doc tightening makes two additional constraints explicit.
First, the branch BV theorem may not quantify over an arbitrary side cone:
its statement must carry the compact-direction local wedge hypothesis saying
that `y + i εη` lies in the ACR branch domain and `y - i εη` lies in the
pulled BHW branch domain, uniformly for compact `K ⊆ E` and compact
`Kη ⊆ C`.  This `hlocal` field is supplied by the one-branch OS45 horizontal
domain theorem: the ordered OS45 formulas give the half-time
directions, but the BHW/Jost common-real-environment input is what puts the
horizontal edge and a small conic side window inside the correct branch
domains.  That input is now explicitly patch-level: the active theorem is the
adjacent identity-order OS45 source-patch theorem putting the selected
horizontal edge in the identity and swapped pulled branch domains.  It is not
an all-Jost pointwise formula, and it is not supplied by hope or by total
function values outside domains.  Second,
the ACR branch representative is the branch-undone quarter-turn pullback
`bvt_F (permAct β.symm ((os45QuarterTurnCLE).symm z))`; its holomorphy on the
ACR branch domain is obtained by rewriting with the permutation-symmetry field
of `bvt_F_acrOne_package`, reducing to the ordinary forward-tube
holomorphy.  The local selector
`BHW.os45_adjacent_identity_horizontalEdge_sourcePatch` is now transcript-level:
it shrinks the checked adjacent identity-order patch to a connected ball with
compact closure, so that it still carries the Wick/real trace-domain and
opposite-tube geometry fields, and also puts the selected OS45 horizontal edge
inside the two pulled BHW branch domains needed for the adjacent identity-order
patch.  This precompactness is what lets the branch-horizontal common germ be
cut off on a real neighborhood of `closure E` to produce the full Schwartz CLM
required by the checked SCV EOW theorem.  The proof-doc route for this packet
is now fixed: the source theorem is split in the theorem-2 blueprint into the
genuine one-branch germ statement `BHW.os45BranchHorizontalCommonGerm` and its
boundary-CLM consumer `BHW.os45BranchHorizontalBoundaryValue`, whose outputs
exactly match the `acr_bv` and `bhw_bv` fields of
`OS45BranchHorizontalBV`.  The route must not introduce public identity or
adjacent branch BV wrappers that merely fix the branch label and forward
generic inputs; any private assembly helper must genuinely derive the selected
branch's `hsource`, `hlocal`, common edge, and openness/compactness data before
calling the generic theorem.  The generic BV consumer now takes
only the common edge `E`, compactness/openness data, `hsource`, and `hlocal`;
Jost/order/extended-tube fields live upstream where `hsource` and `hlocal` are
proved.  Domain membership, local side windows, and precompactness do not by
themselves prove that the ACR and pulled BHW formulas are restrictions of one
holomorphic germ.
The only auxiliary cutoff lemma on this path is the pure real-analysis
Schwartz cutoff statement.  The checked theorem
`SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open` already supplies
the support-in-open projection; the branch-BV route exposes the same
construction with the additional compact-support field as
`SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open_compactSupport`, so
the regular boundary CLM can be built through the checked flat-coordinate
`SCV.exists_closedBall_integral_clm_of_continuousOn` API rather than a fresh
seminorm proof.  Because the branch theorem is on `NPointDomain d n`, the
proof first uses the flattening adapters
`BHW.exists_nPoint_schwartz_cutoff_eq_one_on_compact_subset_open_compactSupport`
and `BHW.exists_nPoint_closedBall_integral_clm_of_continuousOn`, based on
`flattenCLEquivReal n (d + 1)`, `flattenCLEquivReal_norm_eq`,
`SchwartzMap.compCLMOfContinuousLinearEquiv`, support transport by the
associated homeomorphism, and `integral_flattenCLEquivReal`.  The
boundary-limit estimate is an all-space integral localized by `φ = 0` off
`tsupport φ`, bounded by the uniform supremum on `tsupport φ × Kη` times
`∫ y, ‖φ y‖`; it must not treat an arbitrary compact support set as the
measure domain.  The common-germ neighborhood shrink is its own pure topology
lemma `BHW.exists_uniform_realEdgeAddImag_mem_open_of_compact`: compactness of
`tsupport φ × Kη` and openness of the common-germ neighborhood give one radius
so both `realEdgeAddImag y η ε` and `realEdgeAddImag y η (-ε)` stay where
`Hβ` is continuous.  This is separate from the branch-domain local-wedge
theorem.  The coordinate and compactness layer for the local horizontal
wedge is also now checked in
`OSToWightmanLocalityOS45TraceMembership.lean`: `BHW.os45ACRBranchDomain`,
`BHW.os45CommonEdge_mem_acrBranchDomain_of_ordered`,
`BHW.realEdgeAddImag`, and
`BHW.os45BranchHorizontal_localWedge_of_edgeDomain`.  These are pure
quarter-turn/topology facts and do not supply the OS-I source theorem.  The
Figure-2-4 selector and the source-patch shrink now have transcript-level
proof plans.  The next work is still proof-document completion, not Lean
implementation, until the analytic source statements have full proof
transcripts.  The theorem-2 blueprint now fixes those transcripts for
`BHW.OS45BranchHorizontalSourceGermAt`,
`BHW.os45BranchHorizontalCommonGerm`, and the boundary-CLM consumer
`BHW.os45BranchHorizontalBoundaryValue`; the next implementation work must
follow those named theorem surfaces in that order.

The source-patch selector is now checked in Lean.  The implemented theorem is
the combined anchored selector
`BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability`, not two
independently chosen selectors.  It starts from the same equal-time
Figure-2-4 witness used by
`BHW.swFigure24_adjacentPathStableNeighborhood_exists`, takes the finite
intersection of the Jost-set preimage, the two ordinary extended-tube
preimages, and the two OS45 horizontal pulled-domain preimages, and proves
anchor membership in the pulled domains from the zero-time identities
`os45CommonEdgeRealPoint 1 x0 = x0`,
`Q.symm (realEmbed x0) = realEmbed x0`, and
`permAct τ.symm (realEmbed x0) = realEmbed (x0 ∘ τ)`.  Openness comes from
`BHW.isOpen_jostSet`, `BHW.isOpen_extendedTube`,
`BHW.isOpen_os45PulledRealBranchDomain`, and the public finite-dimensional
continuity helpers for `realEmbed`, point permutations, and the identity
common-edge map.  Its current path field is conditional on ordered
identity-sector membership: `Γ` is `BHW.os45Figure24IdentityPath`, and `Δ` is
the checked rotated Figure-2-4 realization from the compact-open
path-stability neighborhood.  The scalar-source docs now require the same
checked compact-open proof to expose the deterministic canonical lift field
`hV_adjLift_ET` on the open chart before the adjacent source-pairing theorem is
ported.  The theorem does not compare branch values or assert that the bare
relabelled identity path is the adjacent branch.

The checked patch theorem
`BHW.os45_adjacent_identity_horizontalEdge_sourcePatch` is then a
finite-dimensional shrink: first choose the positive identity-ordered seed
inside `Ufig ∩ Upath`, then shrink inside
`Ufig ∩ Upath ∩ ordered ∩ swappedOrdered` by
`BHW.exists_connected_open_precompact_subset`.  The Wick-seed, real-edge, and
opposite-tube fields are derived from the checked ordered/extended-tube
lemmas; the closure-level ordered, pulled-domain, and Figure-2-4 path fields
are inherited from the same finite intersection.  This separation is
mandatory: the Figure-2-4 environment supplies branch domains only, while the
topology lemma supplies `closure V` containment; neither theorem invokes
`bvt_W`, `extendF` equality, or final locality.  The remaining
non-topological source content is the branch-value compatibility predicate
`BHW.OS45BranchHorizontalSourceGermAt`; domain membership alone is not enough
to identify the ACR and BHW formulas.  The theorem-2 blueprint now isolates
the predicate as a **branch-specific** canonical-germ statement using
`z ↦ extendF (bvt_F OS lgc n) (permAct β.symm (Q.symm z))`.  This is a
route-hardening correction: using the unpermuted germ
`z ↦ extendF (bvt_F OS lgc n) (Q.symm z)` for every branch would identify
the identity and adjacent branch packets before the EOW step and would revive
the retired tautological cancellation shortcut.

Post-selector proof-doc frontier: the production Lean germ-API migration is
now allowed and has started only for the existing source-variety identity and
uniqueness infrastructure.  Do not implement the Hall-Wightman scalar
representative theorem itself until the following two analytic inputs are
transcript-ready.  First, the ordinary Hall-Wightman scalar representative for the OS-II
forward-tube function must be named explicitly, for example as
`BHW.sourceScalarRepresentativeData_bvt_F`; on the theorem-2 route it carries
the ambient dimension hypothesis `hd : 2 <= d` and produces
`BHW.SourceScalarRepresentativeData (d := d) n (bvt_F OS lgc n)` from
`bvt_F_holomorphic` and the checked Lorentz-invariance theorem for `bvt_F`.
This is a Hall-Wightman/BHW source theorem, not a locality or EOW theorem.  It
must not remain a compressed black-box theorem surface.  The proof-doc
implementation contract is:

0. Dimension and analytic-space audit: Hall-Wightman is printed for
   four-vectors, while theorem 2 is stated for spacetime dimension `d + 1`.
   The proof docs must therefore carry the dimension-general replacement of
   the Hall-Wightman linear algebra: `4` becomes `d + 1`, the Lemma-2 direct
   orbit threshold `3` becomes `d`, and the local scalar-chart maximum rank is
   `min (d + 1) n`.  The theorem-2 blueprint now names the needed standard
   geometry inputs:
   `BHW.sourceComplexMinkowskiInner` as the production pairing name
   (older blueprint shorthand `complexMinkowskiBilinear` is not a separate
   API),
   `BHW.ComplexMinkowskiNondegenerateSubspace`,
   `BHW.standardComplexSymmetricBilinear`,
   checked `BHW.complexLorentzVectorAction`,
   `BHW.complexLorentzVectorAction_add`,
   `BHW.complexLorentzVectorAction_smul`, and
   `BHW.complexLorentzVectorAction_sum` in
   `OSReconstruction/ComplexLieGroups/Connectedness/Action.lean`,
   the existing local model `BHW.complexMinkowskiToDotLinearEquiv`,
   `BHW.sourceComplexMinkowskiInner_eq_dot_after_equiv`,
   `BHW.complexMinkowski_wittExtension`,
   `BHW.complexMinkowski_wittExtension_detOne_of_sourceSpan`,
   `BHW.complexMinkowski_wittExtension_or_improper_of_sourceSpan`,
   `BHW.hwLemma3_extendedTube_adaptedRankRepresentative`,
   `BHW.hwLemma3_adaptedBase_transport_smallPerturbation_extendedTube`,
   `BHW.hwLemma3_adapted_sourceGram_localVectorRealization`,
   `BHW.hwLemma3_sourceGram_localVectorRealization`,
   `BHW.sourceComplexGramVariety_eq_sourceSymmetricRankLEVariety`,
   `BHW.sourceComplexGramVariety_eq_rank_le`,
   `BHW.sourceComplexGramVariety_normal`,
   `BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_maxRank`,
   with the determinantal normality subpacket
   `BHW.AnalyticSingularLocus`,
   `BHW.symmetricRankLEMatrixSet`,
   `BHW.sourceSymmetricRankLEVariety_schurLocalProductModel`,
   `BHW.sourceSymmetricRankLEVariety_singularLocus_eq_lowerRank`,
   `BHW.sourceSymmetricRankExactStratum_complexDimension`,
   `BHW.sourceSymmetricRankLEVariety_lowerRank_codim`,
   `BHW.sourceSymmetricRankLEVariety_lowerRank_codim_ge_two`,
   and `BHW.sourceSymmetricRankLEVariety_reduced_cohenMacaulay`,
   `BHW.sourceSymmetricRankLEVariety_cohenMacaulay`,
   `BHW.sourceSymmetricRankLEVariety_regularInCodimOne`,
   `BHW.normalAnalyticSubvariety_of_serre`, and
   `BHW.normalAnalyticSubvariety_weaklyHolomorphic_localExtension`, then
   `BHW.sourceGramVariety_normal_riemannExtension`, followed by the active
   standard-geometry predicates
   `BHW.IsRelOpenIn`, `BHW.LocallyBoundedOn`,
   `BHW.IsAnalyticSubvarietyIn`,
   `BHW.NormalAnalyticSubvariety`,
   `BHW.CohenMacaulayAnalyticSubvariety`, and
   `BHW.RegularInCodimensionOne`, plus the normality-packet support
   predicates
   `BHW.AnalyticLocalRingRegular`,
   `BHW.ReducedAnalyticSubvariety`,
   `BHW.ComplexAnalyticDimension`,
   `BHW.AnalyticCodimensionIn`, and
   `BHW.AnalyticLocalProductModelAt`.  These predicates must be genuine
   finite-dimensional SCV/local-ring notions or imports from the local SCV
   support library, and they must be polymorphic in the finite-dimensional
   ambient complex vector space.  The ordinary scalar Gram space and the
   oriented Gram-plus-volume space are different ambient types; a scalar-only
   SCV predicate/theorem would not typecheck for the oriented route.  They
   cannot be implemented as vacuous placeholders or as wrappers around the
   target scalar representative theorem.  The active
   finite-dimensional Witt packet is also not currently an import lookup:
   local search found no ready `Witt`/`wittExtension`/`extend_isometry`
   bilinear-form theorem.  The blueprint now decomposes
   `BHW.complexMinkowski_wittExtension` through
   `BHW.standardComplexSymmetric_wittExtension_restricted` and
   `BHW.standardComplexSymmetric_wittExtension`: first expose
   `BHW.standardComplexSymmetricBilinForm`, prove symmetry/reflexivity,
   coordinate-basis nondegeneracy, and the dual-vector functional
   representative, then run
   restricted induction on subspace finrank with an explicit equality
   `Module.finrank ℂ U = Module.finrank ℂ U'` for the two induction
   ambients.  That equality is trivial for the top specialization and is
   preserved after removing matching anisotropic lines or matching
   hyperbolic planes by `LinearMap.BilinForm.finrank_orthogonal`.
   The exact support APIs pinned for the induction are
   `LinearMap.BilinForm.orthogonal`,
   `LinearMap.BilinForm.mem_orthogonal_iff`,
   `LinearMap.BilinForm.isCompl_span_singleton_orthogonal`,
   `LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton`,
   `LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal`,
   `LinearMap.BilinForm.toDual`,
   `LinearMap.BilinForm.apply_toDual_symm_apply`,
   `Submodule.exists_isCompl`, `Submodule.prodEquivOfIsCompl`,
   `Submodule.linearProjOfIsCompl`, `LinearEquiv.toSpanNonzeroSingleton`,
   `LinearMap.ofIsCompl`, and `LinearMap.exists_extend`.  The API call sites
   are pinned in the blueprint in implementation form:
   `(ℂ ∙ u).linearProjOfIsCompl C hC`,
   `Submodule.linearProjOfIsCompl_apply_left hC`,
   `Submodule.linearProjOfIsCompl_apply_right hC`,
   `Submodule.prodEquivOfIsCompl_symm_apply_left/right hC`, and
   `LinearMap.ofIsCompl_left_apply/right_apply hC`.  The radical
   branch now has a Lean-shaped theorem and coordinate functional:
   project along `M = ℂ∙u ⊔ C`, extract the scalar coefficient on
   `ℂ∙u`, extend it to the current nondegenerate induction ambient `U` by
   `LinearMap.exists_extend`, represent it inside `U` by
   `(B.restrict U).toDual hU`, and normalize
   `p := p0 - (B p0 p0 / 2) • u`.  The dual-vector orientation is explicitly
   recorded: `apply_toDual_symm_apply` gives `B p0 v = ellU v`, and symmetry
   supplies the left-oriented pairings used in the final statement.  The
   anisotropic line and hyperbolic-plane split lemmas now also have exact
   Lean statements; the latter proves nondegeneracy of
   `span ℂ ({u,p} : Set U)` by the two-coordinate Gram matrix
   `!![0, 1; 1, 0]`, then applies
   `restrict_nondegenerate_iff_isCompl_orthogonal`.  The two induction
   branches now specify the actual recursive ambients and product
   reconstruction: the anisotropic branch uses
   `U1 = BU.orthogonal (ℂ ∙ u)` and builds `T_C` with
   `LinearEquiv.ofLinear` from codomain-restricted maps, while the radical
   branch maps the chosen complement `C` into
   `BU.orthogonal (span ℂ {u,p})` via
   `(⊤ : Submodule ℂ C).map` of a codomain-restricted subtype map.  Both
   branches assemble the global extension as
   `decU.symm.trans ((Acomponent.prod A1).trans decU')` using
   `Submodule.prodEquivOfIsCompl`.  The
   anisotropic-or-radical dichotomy uses polarization
   `B (x + y) (x + y) = 2 * B x y`, not a vague polynomial argument.
   The high-rank orbit consumer must keep both the final equality orientation
   and the determinant gate explicit.  The ordinary subspace Witt theorem
   first gives a complex-orthogonal ambient extension of the span isometry.
   The theorem-2 proper-orbit consumer is instead
   `BHW.complexMinkowski_wittExtension_detOne_of_sourceSpan`, which also
   consumes `BHW.HWSameSourceGramSOOrientationCompatible` and returns
   `BHW.complexLorentzVectorAction Λ (z i) = w i`.  Without that
   compatibility the honest theorem surface is
   `BHW.complexMinkowski_wittExtension_or_improper_of_sourceSpan`, returning
   either the determinant-`1` extension or
   `BHW.HWSameSourceGramImproperOrbitData`.  The public orbit theorem is
   stated as `w = BHW.complexLorentzAction Λ z`; the proof therefore closes
   the component goal with `.symm`, not by relying on an untracked `simpa`
   orientation.
   The determinant-repair subpacket is now explicit:
   `complexMinkowski_wittExtension_full_of_sourceSpan` first extends the span
   isometry to `HallWightmanFullComplexLorentzGroup d`;
   `fullComplexLorentz_to_complexLorentzGroup_of_det_one` converts determinant
   `1` full elements to `ComplexLorentzGroup d`;
   `sourceFullFrameDet_fullComplexLorentzAction` is the finite determinant
   action formula for the full group;
   `fullComplexLorentz_det_neg_reflection_fixing_sourceSpan` supplies the
   determinant-flipping reflection on a proper source span; and
   `fullComplexLorentz_det_eq_frameMapDet_of_fullRank` identifies the
   determinant of a full-rank extension with
   `HWFullRankSameGramFrameMapDet`.  Thus proper-span determinant repair and
   full-rank oriented determinant compatibility are separate proof branches.
   The reflection proof is decomposed further through
   `sourceSpan_orthogonalComplement_nontrivial_of_proper`,
   `complexMinkowskiOrthogonalSubmodule_nondegenerate`,
   `exists_nonisotropic_in_nondegenerate_subspace`,
   `fullComplexLorentzReflection`,
   `fullComplexLorentzReflection_det`, and
   `fullComplexLorentzReflection_fix_subspace`.  This removes the hidden
   "choose a sign on the complement" step: the complement is nontrivial by the
   rank inequality, nondegenerate by orthogonal-complement linear algebra, and
   contains a nonisotropic vector by polarization.
   The blueprint now pins the lower implementation order for this row.  First
   define `BHW.HallWightmanFullComplexLorentzGroup d` as metric-preserving
   complex matrices with no determinant field, together with
   `hallWightmanFullComplexLorentzVectorAction`, configuration action,
   determinant, multiplication, the determinant-square theorem, and the
   determinant-`1` conversion to `ComplexLorentzGroup d`.  The blueprint now
   includes Lean-shaped, scratch-checked pseudo-code for the matrix
   multiplication proof, `fullComplexLorentz_mul_det`,
   `fullComplexLorentz_mul_vectorAction`,
   `fullComplexLorentz_mul_configAction`, and
   `fullComplexLorentz_to_complexLorentzGroup_of_det_one`.  Second expose
   `BHW.sourceComplexMinkowskiBilinForm` from the already implemented
   `sourceComplexMinkowskiInner`, prove ambient nondegeneracy directly from
   the checked `sourceComplexMinkowskiInner_left_nonDegenerate` using
   `LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft`, and define
   `complexMinkowskiOrthogonalSubmodule` through
   `LinearMap.BilinForm.orthogonal`.  Third prove the proper-span complement
   and reflection packet.  The complement theorem now has an implementation
   transcript: `restrictedMinkowskiRank_eq_finrank_of_nondegenerate` proves the
   restricted radical is bottom, then
   `sourceSpan_orthogonalComplement_nontrivial_of_proper` uses
   `sourceGramMatrixRank_eq_restrictedMinkowskiRank_range`, `S.M_eq_range`,
   `S.M_nondegenerate`, `LinearMap.BilinForm.finrank_orthogonal`, and
   `Module.nontrivial_of_finrank_pos`.  The polarization theorem
   `exists_nonisotropic_in_nondegenerate_subspace` is scratch-checked: if
   `B(x,x)` vanished identically, then applying it to `x+y` gives
   `(2 : ℂ) * B(x,y)=0`, hence `B(x,y)=0`, contradicting nondegeneracy.  The
   Householder determinant is computed as a module-reflection determinant:
   `LinearMap.det_eq_det_mul_det` for `W := ℂ ∙ u`, determinant `-1` on
   the invariant line via `LinearEquiv.toSpanNonzeroSingleton`, and identity
   on the quotient via `Submodule.mapQ_apply`.  These are ordinary
   finite-dimensional linear algebra support lemmas, not source imports and
   not public theorem-2 wrappers.
   The full-complex Witt extension is now decomposed as well: since
   `HWHighRankSpanIsometryData` supplies nondegenerate `S.M` and `S.N`, use
   `Submodule.prodEquivOfIsCompl` to split the ambient space as each source
   span plus its orthogonal complement, choose an isometry between the two
   nondegenerate complements by the classification of finite-dimensional
   nondegenerate complex symmetric bilinear forms, and assemble the product
   map into `HallWightmanFullComplexLorentzGroup` by converting a
   source-inner-preserving linear equivalence to a matrix.  The classification
   helper is now proof-doc pinned locally: take Mathlib orthogonal bases,
   use nondegeneracy to prove all diagonal entries are nonzero, use
   `IsAlgClosed.exists_pow_nat_eq` over `ℂ` to rescale them to diagonal
   `1` with `Basis.isUnitSMul`, and compare both forms by
   `LinearMap.sum_repr_mul_repr_mul` in the normalized bases.  This is finite
   linear algebra only and no new axiom is authorized or needed.
   Until these finite linear-algebra sublemmas are implemented sorry-free, the
   high-rank orbit theorem remains blocked after the span-isometry
   construction.
   The active
   germ API
   `BHW.SourceVarietyGermHolomorphicOn`,
   `BHW.SourceVarietyGermHolomorphicOn.continuousOn`,
   `BHW.SourceVarietyGermHolomorphicOn.of_subset_relOpen`,
   `BHW.SourceVarietyGermHolomorphicOn.sub`, and
   `BHW.SourceVarietyGermHolomorphicOn.precomp_sourcePermuteComplexGram`,
   plus the pullback and identity-principle consumers
   `BHW.SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram`,
   `BHW.SourceVarietyGermHolomorphicOn.comp_differentiableOn_chart`, and
   `BHW.sourceComplexGramVariety_identity_principle`; the continuity
   theorem must carry or derive the hypothesis
   `U ⊆ BHW.sourceComplexGramVariety d n`, supplied in this route by relative
   openness in the source variety.
   This fixes the singular-rank analytic gap in the route without asking for
   a false off-variety equality statement: for `n > d + 1`, Hall-Wightman's
   output is a holomorphic germ on the symmetric determinantal scalar-product
   variety, represented locally by ambient holomorphic charts that agree only
   on the variety.  Boundedness and continuity at singular points are used by
   the normal analytic-space Riemann/removable theorem, together with density
   of the maximal-rank locus in every relatively open source-variety patch, to
   produce those local variety-germ representatives; they do not produce one
   global ambient function holomorphic off the variety.

   The determinantal normality subpacket is now pinned to a precise proof
   order.  First, the checked Schur-graph infrastructure supplies the local
   product model: on a determinant-unit principal patch,
   `sourcePrincipalSchurGraph_rankLE_image_eq_openCoordinatePatch` identifies
   `sourceSymmetricRankLEVariety n D` with a smooth `(A,B)` factor times the
   smaller cone `BHW.symmetricRankLEMatrixSet q (D-r)` in the Schur
   coordinate, with `q` the complementary finite index type.  Second,
   this model proves the singular-locus equality
   `Sing(rank <= D) = rank <= D-1` in the range `0 < D < n`, while `D = 0`
   and `n <= D` are smooth cases.  Third, the selected-chart dimension formula
   gives codimension `n - D + 1`, hence at least two in the singular range.
   Fourth, the standard symmetric-determinantal reduced Cohen-Macaulay theorem
   is now pinned at coordinate-ring level: use the polynomial ring on
   unordered symmetric source-coordinate pairs, the generic symmetric matrix,
   and the ideal generated by all `(D+1) x (D+1)` minors.  The required
   algebraic theorem is primality plus Cohen-Macaulayness of this symmetric
   determinantal coordinate ring, equivalently the
   Jozefiak-Pragacz/straightening-law theorem over `ℂ`; the analytic
   translation localizes this to reduced Cohen-Macaulay analytic local rings.
   Then `sourceSymmetricRankLEVariety_regularInCodimOne` is assembled from the
   singular-locus equality plus the codimension bound, and
   `sourceComplexGramVariety_normal` is Serre normality transported through
   `sourceComplexGramVariety_eq_sourceSymmetricRankLEVariety`.  Any Lean
   implementation must follow this packet or consume an already implemented
   sorry-free theorem with exactly this finite-dimensional
   algebraic-geometry content; it cannot replace the packet by a source-scalar
   representative wrapper.

   Normal/removable production readiness is now componentwise.  Before Lean
   may use `BHW.sourceGramVariety_normal_riemannExtension` or
   `BHW.sourceGramVariety_removableAlongExceptionalRank`, the proof must first
   identify `sourceComplexGramVariety d n` with the symmetric rank-`<= d+1`
   variety, prove `BHW.sourceComplexGramVariety_normal` through the Schur
   local product model, singular-locus equality, rank-exact dimension,
   codimension-at-least-two calculation, reduced Cohen-Macaulay coordinate
   ring theorem, and Serre assembly, and prove density of the maximal-rank
   locus by the Schur-product perturbation argument: at rank `r < min (d+1) n`,
   add a tiny diagonal rank-`min(d+1,n)-r` Schur-complement path, transport it
   back through the determinant-unit chart, and then localize the global
   closure statement to every relatively open patch by
   `closure_inter_open_of_mem_open`.  This is the theorem
   `BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_maxRank`; it is
   not an automatic consequence of analyticity of the exceptional locus.  Only
   then may the OS-free finite-dimensional-polymorphic normal-space Riemann theorem
   `BHW.normalAnalyticSubvariety_weaklyHolomorphic_localExtension` be applied
   to the branch-defined scalar value `phi`, returning local ambient charts
   with the domain-control field
   `U0 ∩ BHW.sourceComplexGramVariety d n ⊆ U`.  This packet must not mention
   OS, Wightman fields, EOW, PET, theorem-2 locality, `bvt_W`, or
   `sourceScalarRepresentativeData_bvt_F`; it is finite-dimensional
   SCV/algebraic geometry plus the already supplied branch-defined scalar
   value.

   The theorem-2 blueprint still archives the stronger Siu/Cartan package
   `BHW.SteinOpen`,
   `BHW.sourceComplexGramVariety_closedAnalytic`,
   `BHW.sourceExtendedTubeGramDomain_domainOfHolomorphy`,
   `BHW.domainOfHolomorphy_steinAnalyticSubspace`,
   `BHW.sourceExtendedTubeGramDomain_steinAnalyticSpace`,
   `BHW.siu_steinNeighborhood_sourceGramSubspace`,
   `BHW.sourceExtendedTubeGramDomain_steinAmbientNeighborhood`,
   `BHW.sourceGramIdealSheaf_coherent`,
   `BHW.cartanB_restriction_surjective_for_coherentIdeal`,
   `BHW.cartan_surjective_restriction_sourceGramVariety`, and
   `BHW.sourceVariety_holomorphicGerm_cartanAmbientExtension`; this is now an
   optional strong-API bridge only.  It is not accepted as a Hall-Wightman
   source consequence, because the local source audit records `S'_n` as open
   and connected but not as the natural domain of holomorphy for the field
   theory functions.  Gemini Deep Research interaction
   `v1_ChZIeHYwYWE5cng1Mzd4Z19ldGRDQURREhZIeHYwYWE5cng1Mzd4Z19ldGRDQURR`
   agrees that the strong bridge is mathematically sound if Step 1 is supplied
   by an independent Bochner-Martin/invariant-quotient theorem for the scalar
   image `S'_n` (or equivalent modern extended-tube SCV input).  That verdict
   keeps the bridge available as optional SCV support, but it does not reopen
   production Lean until those additional source statements are proof-ready or
   explicitly approved as a source-import boundary.

   Implementation gate: none of the Hall-Wightman scalar representative
   surfaces in this item may move to production Lean until either the listed
   BHW/Hall-Wightman germ-support theorems have proof transcripts detailed
   enough to implement without new `sorry`/`axiom`, or the user explicitly
   approves a source-import boundary with exactly these theorem statements and
   no theorem-2/locality content.  The existing production
   `SourceScalarRepresentativeData.Phi_holomorphic` field has now been
   migrated from `BHW.SourceVarietyHolomorphicOn` to
   `BHW.SourceVarietyGermHolomorphicOn`; that migration removes the false
   global-ambient holomorphy requirement but does not by itself implement
   `BHW.sourceScalarRepresentativeData_bvt_F`.

   Current no-axiom clarification: no such source-import boundary is approved
   on this branch.  Until the user explicitly approves one with exact
   proposition-level statements, the phrase "source import" is only a
   proof-document audit label.  Production Lean must contain real proofs of
   the named surfaces, or consume already implemented sorry-free local support
   theorems with the same mathematical content.  It may not add a new
   `axiom`, a theorem-level `sorry`, an `admit`, or a data-valued
   `noncomputable def` that hides the Hall-Wightman proof in a choice.  Any
   future approved boundary must be standard BHW/Hall-Wightman, finite
   linear-algebra, or SCV support only; it must not mention theorem-2
   locality, PET independence, local EOW, final `bvt_W`, or OS-specific
   branch conclusions.

   The improper-component input now has an implementation-level source shape:
   introduce a genuine `BHW.HallWightmanFullComplexLorentzGroup d` as
   metric-preserving complex matrices with no determinant-`1` field, prove
   `det ^ 2 = 1`, embed the existing `ComplexLorentzGroup d` as the
   determinant-`1` component, and define the full action separately from
   `BHW.complexLorentzAction`.  The real source predicate must quantify over
   `LorentzLieGroup.FullLorentzGroup d` with
   `LorentzLieGroup.IsOrthochronous d Λ`, not over
   `RestrictedLorentzGroup d`.  A support theorem
   `BHW.fullOrthochronousRealLorentz_preserves_forwardTube` is still missing:
   the existing `ForwardTubeLorentz.orthochronous_preserves_forward_tube`
   comments that properness is unused, but its Lean type is still specialized
   to `LorentzGroup d`, so it cannot discharge determinant-`-1` invariance.
   The repo already has bridge infrastructure in
   `Bridge/AxiomBridge.lean`: `lorentzGroupEquiv`,
   `lorentzGroupEquiv_val`, `lorentzGroupEquiv_symm_val`,
   `isProperLorentz_iff_isProper`, and `isOrthochronous_iff` transport between
   `LorentzLieGroup.FullLorentzGroup d` and the Wightman-layer
   `FullLorentzGroup d`.  These names are transport support only; they do not
   prove the missing `bvt_F` improper invariant.
   Therefore `BHW.bvt_F_realOrthoChronousInvariant` is a real missing source
   input, not a consequence of
   `bvt_F_complexLorentzInvariant_forwardTube`.
   This is not merely absent infrastructure: the local OS axiom structure
   currently assumes Euclidean rotation invariance only for `SO(d+1)`
   (`R.det = 1`), and the comment on
   `OsterwalderSchraderAxioms.E1_rotation_invariant` explicitly notes that
   full `O(d+1)` parity is not implied.  Thus the proof docs must still
   locate a paper-sourced OS/BHW reason why the scalar branches have the
   needed improper real orthochronous invariance, or else correct the
   Hall-Wightman scalar-descent statement so it does not require parity.
   Adding parity or silently treating `SO(d+1)` as `O(d+1)` is forbidden.
   The source-text comparison is now explicit and was rechecked against the
   local PDF extraction on 2026-05-02: Hall-Wightman Theorem I is the
   scalar-product theorem, and its Lemma 1 treats the space-inversion/improper
   component inside the invariant analytic-function argument.  Streater-
   Wightman Theorem 2-11 and the OS I §4.5 reconstruction invocation are
   stated for the restricted/proper Lorentz group and proper complex group
   `L_+(C)`.  The OS `L_+(C)` continuation cannot be cited as full source-
   Gram descent without resolving this component mismatch.
   The implementation-level local-code audit now makes this mismatch exact:
   `bvt_F_restrictedLorentzInvariant_forwardTube` quantifies only over
   `RestrictedLorentzGroup d`, `bvt_F_complexLorentzInvariant_forwardTube`
   quantifies only over the determinant-`1` `ComplexLorentzGroup d`, and
   `OsterwalderSchraderAxioms.E1_rotation_invariant` assumes both
   `R.transpose * R = 1` and `R.det = 1`.  The bridge theorems
   `lorentzGroupEquiv`, `lorentzGroupEquiv_val`,
   `lorentzGroupEquiv_symm_val`, `isProperLorentz_iff_isProper`, and
   `isOrthochronous_iff` only transport matrix predicates between full
   Lorentz APIs; they do not prove a `bvt_F` invariant under determinant-`-1`
   orthochronous transformations.  Hence the exact missing full-component
   theorem, if the pure scalar-product route is used, is
   `BHW.bvt_F_realOrthoChronousInvariant [NeZero d] (hd : 2 <= d)
   (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
   (n : Nat) :
   BHW.HallWightmanRealOrthoChronousInvariant d n (bvt_F OS lgc n)`.
   Its proof cannot be obtained by coercing a restricted Lorentz transform to
   a full one or by dropping the determinant hypothesis; that would add parity
   by hand.  Conversely, the theorem
   `SourceScalarRepresentativeData` from holomorphy plus proper
   `ComplexLorentzGroup d` invariance alone is forbidden: the
   determinant/Vandermonde diagnostic below is a counterexample schema to
   exactly that theorem.
   The blueprint now records the finite-dimensional diagnostic explicitly:
   for `d + 1 <= n`, the determinant of any ordered full source frame is an
   entire determinant-`1` complex Lorentz invariant, transforms by
   multiplication with `det A` under the full complex Lorentz group, and is
   not determined by the ordered Gram matrix unless the improper component is
   also quotiented.  This is the concrete counterexample schema showing that
   the proper-only full-Gram descent theorem would be false.
   The same diagnostic now also rules out finite source-permutation symmetry
   as a repair: in the top-rank case `n = d + 1`, the product of the ordered
   frame determinant with the Vandermonde of the diagonal Gram entries is
   holomorphic, invariant under all source permutations, invariant under
   determinant-`1` complex Lorentz transformations, and still changes sign
   under an improper same-Gram full Lorentz transformation.  Therefore
   `bvt_F_perm` or pointwise permutation symmetry cannot be used to bypass the
   full-component/oriented source decision.
   This is now a hard route-decision gate, not an implementation detail.  For
   the strict OS I §4.5 theorem-2 route, the decision is to formalize the
   proper-complex `L_+(C)` continuation through the oriented scalar-source API:
   Gram data plus all ordered full-frame determinants, with every downstream
   consumer migrated accordingly.  A full-component Hall-Wightman theorem
   supplying `BHW.bvt_F_realOrthoChronousInvariant` remains only a conditional
   side route for the pure-Gram constructor, and an "obstruction vanishes"
   route remains closed until a paper source proves that exact cancellation
   without adding parity, final locality, PET independence, or standalone
   `bvt_F_perm`.
   Strict-route selection guard: under the user's non-negotiable OS I §4.5 /
   BHW-Jost route, the active target is the paper's BHW/Jost continuation
   step, not an arbitrary strengthening.  The source audit now distinguishes
   two paper-level statements that cannot be merged in Lean: Hall-Wightman's
   own Theorem I is the scalar-product theorem, while OS I §4.5 invokes BHW
   as a single-valued symmetric proper-complex `L_+(C)` continuation on the
   extended/permuted domain.  The active theorem-2 source layer is therefore
   the proper/oriented invariant API; the pure-Gram
   `SourceScalarRepresentativeData` surface may not be reused on this route.
   If the oriented package cannot be proved or source-imported, the proof docs
   remain blocked rather than falling back to the pure-Gram theorem surface.
   Current branch status: no local production theorem supplies
   `BHW.bvt_F_realOrthoChronousInvariant`, and the OS axiom surface does not
   contain full Euclidean `O(d+1)` invariance.  Hence
   `BHW.sourceScalarRepresentativeData_bvt_F` is presently only a conditional
   target for the full-component resolution, not an active production Lean
   target.  Since the theorem-2 proof route now adopts the oriented
   scalar-source API, `SourceScalarRepresentativeData` and every adjacent
   `S'_n` consumer must be restated with the oriented invariant; the existing
   pure-Gram data structure may not be reused with orientation hidden in
   comments or hypotheses.  The theorem-2 blueprint now records the active
   implementation shape:
   `BHW.SourceOrientedGramData`,
   `BHW.SourceOrientedGramData.gram`,
   `BHW.SourceOrientedGramData.det`,
   `BHW.SourceOrientedGramData.ext`,
   `BHW.sourceOrientedMinkowskiInvariant`,
   `BHW.sourceOrientedExtendedTubeDomain`,
   `BHW.SourceOrientedVarietyGermHolomorphicOn`,
   `BHW.IsRelOpenInSourceOrientedGramVariety.subset`,
   `BHW.IsRelOpenInSourceOrientedGramVariety.to_isRelOpenIn`,
   `BHW.IsRelOpenInSourceOrientedGramVariety.inter`,
   `BHW.SourceOrientedVarietyGermHolomorphicOn.of_subset_relOpen`,
   `BHW.SourceOrientedVarietyGermHolomorphicOn.sub`,
   `BHW.sourcePermuteOrientedGram`,
   `BHW.continuous_sourcePermuteOrientedGram`,
   `BHW.differentiable_sourcePermuteOrientedGram`,
   `BHW.IsRelOpenInSourceOrientedGramVariety.preimage_sourcePermuteOrientedGram`,
   `BHW.extendedTube_same_sourceOrientedInvariant_extendF_eq`, and
   `BHW.SourceOrientedScalarRepresentativeData`, now extended with the
   oriented producer ladder
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected`,
   `BHW.sourceOrientedVarietyGermHolomorphicOn_extendF_descent`,
   `BHW.sourceOrientedScalarRepresentativeData_of_branchLaw`, and
   `BHW.hallWightman_sourceOrientedScalarRepresentativeData`, and
   with the production ordering requirement that the generic
   finite-dimensional SCV predicates are imported before the
   `to_isRelOpenIn` conversion is declared,
   `BHW.sourceOrientedScalarRepresentativeData_bvt_F`.
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected`,
   `BHW.SourceOrientedScalarRepresentativeData`,
   `BHW.sourceOrientedQuotientValue`,
   `BHW.sourceOrientedQuotientValue_wellDefined`,
   `BHW.LocallyBoundedOn`,
   `SCV.continuousWithinAt_of_local_eqOn_relNeighborhood`,
   `SCV.locallyBoundedAt_of_local_eqOn_relNeighborhood`,
   `SCV.continuousWithinAt_of_compact_parameter_surjection`,
   `BHW.sourceOrientedResidualChart_compactBound`,
   `BHW.sourceOrientedResidualChart_quotient_eq_parameter`,
   `BHW.sourceOrientedQuotientValue_locallyBounded_of_residualChart`,
   `BHW.sourceOrientedQuotientValue_continuous_of_residualChart`,
   `BHW.sourceOrientedQuotientValue_continuous_locallyBounded_of_maxRankLocal`,
   `BHW.sourceOrientedResidualChart_clusterValue`, and
   `BHW.sourceOrientedScalarRepresentativeData_of_branchLaw` are now checked;
   the later descent and Hall-Wightman specialization names remain active
   proof-doc targets and are not production-Lean-ready until their producer
   ledger is complete.  Their purpose is also to make clear that an oriented
   proof cannot be fed through the existing pure-Gram
   `SourceScalarRepresentativeData.branch_eq` API.
   Lean-shape correction: `SourceOrientedGramData` is now a product-coordinate
   type, not a raw record with untransported topology.  The `.gram` and `.det`
   names are projection definitions on that product, so `IsOpen`,
   `DifferentiableOn`, relative openness, connectedness, and germ-holomorphic
   predicates are all stated on an actual finite-dimensional complex vector
   space.
   The binding oriented producer ledger is:
   `sourceFullFrameMatrix`, `sourceFullFrameDet`, its
   complex-Lorentz/permutation algebra, and its continuity theorem; the
   assembly lemmas
   `sourceOrientedMinkowskiInvariant_complexLorentzAction` and
   `sourceOrientedMinkowskiInvariant_permAct`;
   `same_sourceOrientedInvariant_detOneOrbit_or_singularLimit`;
   `extendedTube_same_sourceOrientedInvariant_extendF_eq`;
   `sourceOrientedExtendedTubeDomain_relOpen_connected` (checked);
   `sourceOrientedVarietyGermHolomorphicOn_extendF_descent`; and only then
   the already checked assembly surface
   `sourceOrientedScalarRepresentativeData_of_branchLaw` plus the remaining
   specializations
   `hallWightman_sourceOrientedScalarRepresentativeData`, and
   `sourceOrientedScalarRepresentativeData_bvt_F`.  The specialization to
   `bvt_F` uses `bvt_F_holomorphic`,
   `bvt_F_complexLorentzInvariant_forwardTube`, and `BHW_forwardTube_eq`;
   it must not import the missing full-component/improper invariant.
   Current oriented permutation API clarification, 2026-05-02:
   `BHW.sourcePermuteOrientedGram_mem_variety_iff` is now pinned as a real
   automorphism proof on the oriented source variety.  In the reverse
   direction, if
   `sourcePermuteOrientedGram d n τ G =
   sourceOrientedMinkowskiInvariant d n z`, use the witness
   `BHW.permAct (d := d) τ⁻¹ z`, rewrite by
   `BHW.sourceOrientedMinkowskiInvariant_permAct`, cancel the Gram component
   with `BHW.sourcePermuteComplexGram_inv_mul`, and cancel the determinant
   component by composing the embeddings `τ⁻¹.toEmbedding` and
   `τ.toEmbedding`.  The forward direction uses the witness
   `BHW.permAct (d := d) τ z`.  This is the support needed by
   `BHW.IsRelOpenInSourceOrientedGramVariety.preimage_sourcePermuteOrientedGram`
   and by oriented germ precomposition; it is finite source-coordinate
   algebra, not a scalar-representative or locality input.
   Current oriented scalar-representative assembly clarification, 2026-05-02:
   `BHW.sourceOrientedScalarRepresentativeData_of_branchLaw` is checked in
   `SourceOrientedScalarRepresentative.lean`, and the theorem-2 blueprint
   still gives the Lean-shaped body for
   `BHW.hallWightman_sourceOrientedScalarRepresentativeData`.  The checked
   constructor only chooses the descended `Phi`, sets `U_eq := rfl` for the
   exact oriented extended-tube domain, stores the relative-open and connected
   fields from `hGeom`, and copies the branch equation from
   `Classical.choose_spec hDesc`.  The Hall-Wightman constructor first proves
   the oriented extended-tube branch law, then calls
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected` and
   `BHW.sourceOrientedVarietyGermHolomorphicOn_extendF_descent`, and only
   then assembles the representative.  The quotient value
   `BHW.sourceOrientedQuotientValue_wellDefined` is also checked with the
   exact `dif_pos`/`Classical.choose_spec` proof: compare the chosen
   preimage with the supplied one by the oriented branch law.  These are
   assembly proofs; they do not reduce the required lower producer list.
   The same cleanup pins the mechanical
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected` body as the
   producer-instantiated pair of relative openness and connectedness; the only
   real mathematical content in that theorem is the local realization theorem
   feeding the relative-open half.  Lean has checked this topology split in
   `SourceOrientedLocalRealization.lean` as
   `BHW.SourceOrientedExtendedTubeLocalRealizationData`,
   `BHW.SourceOrientedExtendedTubeLocalRealizationProducer`,
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_of_localRealization`, and
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected_of_localRealization`.
   The final no-parameter theorem is now checked in
   `SourceOrientedRankDeficientTubeResidualPolydisc.lean` as
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected`, by applying
   `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected_of_rankDeficientResidualChartProducer`
   to `BHW.sourceOriented_rankDeficient_residualChartProducer`.
   The full-frame max-rank tube shrink is now also checked in the same file as
   `BHW.continuousOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero`,
   `BHW.sourceOrientedExtendedTubeLocalRealizationData_of_fullFrameDetNonzero`,
   and
   `BHW.sourceOrientedExtendedTubeLocalRealizationData_of_fullFrameMaxRank`.
   The small-arity max-rank reducer and the full max-rank dispatcher are now
   checked as
   `BHW.sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt_any`,
   `BHW.sourceOrientedExtendedTubeLocalRealizationData_of_smallArityMaxRank`,
   and `BHW.sourceOrientedExtendedTubeLocalRealizationData_of_maxRank`.
   The full-frame proof uses `isOpen_extendedTube`, pulls an open model
   neighborhood back through the reconstructed-vector map, and uses the stored
   chart inverse to recover the oriented invariant.  The small-arity proof
   uses the ordinary source-Gram local image theorem inside `ExtendedTube` and
   the fact that there are no embeddings `Fin (d + 1) ↪ Fin n` when
   `n < d + 1`.  The rank-deficient residual extended-tube realization and
   the final max-rank/rank-deficient dispatch are now checked.  No downstream
   proof should re-prove the open-union argument or hide this datum behind a
   scalar representative.
   The oriented branch-law surface has been tightened: it must return an
   actual `∃ Λ : ComplexLorentzGroup d, w = complexLorentzAction Λ z` orbit
   alternative or the singular contraction data.  Returning only
   `HWSameSourceGramSOOrientationCompatible` is too weak, because low-rank
   fibres are orientation-compatible but still require the singular-limit
   proof.  The blueprint now pins the determinant-ratio sublemmas needed to
   turn equality of oriented full-frame determinants into determinant `1` for
   the full-rank same-Gram frame map.
   The oriented domain geometry has also been split: connectedness is a
   mechanical continuous-image theorem from `isConnected_extendedTube` and
   `continuous_sourceOrientedMinkowskiInvariant`; relative openness is the
   checked
   `sourceOrientedExtendedTubeDomain_relOpen_of_localRealization` theorem
   applied to the checked producer
   `sourceOrientedExtendedTubeLocalRealizationProducer_of_rankDeficientResidualChartProducer`.
   That producer constructs actual nearby extended-tube vectors realizing the
   full oriented invariant, using selected full-frame charts in full rank and
   Hall-Wightman adapted residual-frame charts in rank-deficient cases.
   The rank-deficient local-image packet checked by the sliced Schur stack is
   not sufficient for this purpose by itself: its inverse normal-form transport
   is a `SourceOrientedVarietyTransportEquiv` induced by an invertible
   source-label matrix, and arbitrary source-label linear changes do not
   preserve `ExtendedTube`.  The production target is therefore the stronger
   `SourceOrientedRankDeficientResidualChartData`, carrying an explicit
   residual-parameter vector map `toVec`, proofs `toVec_mem :
   ∀ c ∈ K, toVec c ∈ ExtendedTube d n`, and `image_surj :
   Ω ∩ sourceOrientedGramVariety d n ⊆
     (fun c => sourceOrientedMinkowskiInvariant d n (toVec c)) '' P`.
   The invariant-membership field is over the open Schur domain `P`, not the
   compact control set `K`: requiring it on all of `K` together with
   `P ⊆ K` and `image_surj` would force the intended local Schur patch to be
   a compact image.
   A checked conversion
   `SourceOrientedRankDeficientResidualChartData.to_realizationData` then
   derives `SourceOrientedRankDeficientRealizationData`, and
   `.to_localRealization` derives
   `SourceOrientedExtendedTubeLocalRealizationData`.  The long hard target is
   named by the checked alias
   `SourceOrientedRankDeficientResidualChartProducer`, and the chart exposes
   checked accessors `center_mem` and `toVec_c0_mem` so downstream proofs do
   not reopen the center bookkeeping.  No proof step may replace this
   ET-valued residual family by an arbitrary variety lift.
   The max-rank section theorem is now split by arity: when `n < d + 1`, the
   oriented chart reduces to the ordinary Gram max-rank chart because there
   are no full-frame determinant coordinates; when `d + 1 <= n`, the checked
   full-frame local-realization def above supplies the actual
   extended-tube-valued local section at the `SourceOrientedExtendedTubeLocalRealizationData`
   interface.  The max-rank dispatcher, rank-deficient residual realization,
   and final case split are now checked, so no further Lean work remains in
   the local-realization producer.
   full-frame chart must use `SourceOrientedFullFrameGaugeChartData`, a
   gauge-fixed special-orthogonal section with determinant coordinate
   `G.det ι`.  The rank-deficient half is named separately as
   `SourceOrientedRankDeficientRealizationData`; it must realize nearby
   oriented-variety points by residual isotropic-frame variables inside
   `ExtendedTube`, not by arbitrary ordinary Gram lifts.
   The top-level local-realization theorem is now an assembly theorem over
   these two cases: `SourceOrientedRankDeficientResidualChartData.to_localRealization`
   converts the residual chart into local realization, and
   `sourceOrientedExtendedTubeLocalRealizationProducer_of_rankDeficientResidualChartProducer`
   dispatches by `SourceOrientedMaxRankAt`.  The relative-openness proof
   indexes its open union by the subtype of actual extended-tube points; it
   does not use implicit proof placeholders or an arbitrary lift of an
   oriented invariant.
   The full-frame gauge chart now has an implementation contract:
   `SourceFullFrameOrientedGramData`,
   `SourceFullFrameOrientedCoord`,
   `SourceFullFrameOrientedGramData.toCoord`,
   `SourceFullFrameOrientedGramData.ofCoord`,
   `sourceFullFrameOrientedGramCoord`,
   `sourceFullFrameOrientedGramVarietyCoord`,
   `sourceFullFrameOrientedGramVarietyCoord_eq_image`,
   `sourceFullFrameOrientedGram`,
   `sourceFullFrameOrbitTangent`,
   `sourceFullFrameOrientedDifferentialLinear`,
   `sourceFullFrameOrientedDifferentialCLM`,
   `SourceFullFrameGaugeSliceData`,
   `sourceFullFrameGaugeSlice_exists`,
   `sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent`,
   `sourceFullFrameOrientedDifferential_range_eq_tangent`,
   `sourceFullFrameSlice_differential_linearEquiv`,
   `sourceFullFrameOrientedEquation`,
   `sourceFullFrameOrientedHypersurfaceCoord`,
   `sourceFullFrameOrientedGramCoord_mem_hypersurface`,
   `RegularZeroLocusAt` with explicit `deriv`, `value_zero`,
   `has_deriv`, and `deriv_surj` fields,
   `sourceFullFrameOrientedHypersurface_regularAt`,
   `sourceFullFrameSlice_localImage_eq_hypersurface`,
   `sourceFullFrameSlice_localImage_eq_variety`, and
   `sourceFullFrameGaugeSection_of_localImage`.  The proof must use the
   derivative calculation for `M η Mᵀ` and `det M`, choose a complement to the
   infinitesimal determinant-`1` Lorentz orbit, and apply the finite-dimensional
   holomorphic constant-rank/local-image theorem on that slice.  The
   implementation order is fixed: define the oriented equation, hypersurface,
   and tangent model before `SourceFullFrameGaugeSliceData`, prove the slice
   local image into the smooth hypersurface first, and only then restrict the
   inverse/right-inverse fields to the actual image variety.  This prevents a
   circular proof of local variety-equals-hypersurface before the slice
   inverse theorem is available.  All
   openness, differentiability, tangent, and local-image statements in this
   packet live in the explicit product vector space
   `SourceFullFrameOrientedCoord d`; the raw
   `SourceFullFrameOrientedGramData` structure is used only as an algebraic
   record and is converted by `toCoord`/`ofCoord`.  The slice map
   is not a submersion to the whole ambient `gram × det` space; it is first
   locally biholomorphic onto the oriented full-frame hypersurface sheet, and
   then onto the oriented full-frame image variety by restriction.  The
   tangent target is now explicit:
   `sourceFullFrameOrientedTangentSpace`,
   `sourceFullFrameOrientedHypersurface_regularAt`,
   `sourceFullFrameOrientedTangentSpace_eq_linearizedEquation`,
   `sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph`,
   `sourceFullFrameGaugeSliceImplicitKernelMap_surjOn_chartTarget`,
   `sourceFullFrameGaugeSliceImplicitKernelMap_right_inv_on_chartTarget`, and
   `sourceFullFrameGaugeSliceImplicitKernelMap_left_inv_on_chartSource`.  The
   local equation is
   `det gram = minkowskiMetricDet d * det^2`, and its linearization is the
   trace formula used as the target tangent space.  The proof must not choose
   an unproved square-root branch or an unverified holomorphic Gram-Schmidt
   section.  The associated max-rank local section data must also shrink the
   whole ambient coordinate neighborhood into `ExtendedTube`, not merely the
   variety slice; otherwise the proof of holomorphy for `extendF F` composed
   with the section has no valid domain membership hypothesis.
   Lean implementation checkpoint, 2026-05-03: the finite-dimensional
   full-frame coordinate/tangent substrate is now checked in
   `BHWPermutation/SourceOrientedFullFrame.lean`.  The checked names include
   `sourceFullFrameGram`, `continuous_sourceFullFrameGram`,
   `contDiff_sourceFullFrameGram`,
   `differentiable_sourceFullFrameGram`,
   `SourceFullFrameOrientedGramData`,
   `SourceFullFrameOrientedCoord`,
   `sourceFullFrameOrientedGramCoord`,
   `sourceFullFrameOrientedGramVarietyCoord_eq_image`,
   `continuous_sourceFullFrameOrientedGramCoord`,
   `contDiff_sourceFullFrameOrientedGramCoord`,
   `differentiable_sourceFullFrameOrientedGramCoord`,
   `sourceFullFrameOrientedCoord_detNonzero_open`,
   `sourceFullFrameSymmetricCoordSubmodule`,
   `sourceFullFrameOrientedEquation`,
   `sourceFullFrameOrientedHypersurfaceCoord`,
   `sourceFullFrameOrientedEquationDerivLinear`,
   `sourceFullFrameOrientedEquationDerivCLM`,
   `sourceFullFrameDetDirection`,
   `sourceFullFrameSymmetricDetDirection`,
   `sourceFullFrameOrientedEquationDeriv_detDirection`,
   `sourceFullFrameOrientedEquationDerivOnSymmetric_surjective_of_det_ne_zero`,
   `specialComplexLorentzLieAlgebra`,
   `infinitesimalRightSpecialLorentzAction`,
   `sourceFullFrameOrbitTangent`,
   `sourceFullFrameOrientedDifferentialLinear`,
   `sourceFullFrameOrientedDifferentialCLM`,
   `sourceFullFrameOrientedTangentSpace`,
   `SourceFullFrameGaugeSliceData`,
   `sourceFullFrameGaugeSliceMap`, and
   `sourceFullFrameOrientedGramCoord_differentiableAt_translate`.
   The same file now also checks
   `minkowskiMetricDet_mul_self`,
   `isUnit_minkowskiMetricDet`,
   `minkowskiMetricDet_ne_zero`,
   `sourceFullFrameGram_eq_mul_eta_transpose`,
   `sourceFullFrameGram_det_eq`,
   `sourceFullFrameGram_det_isUnit_of_frame_det_isUnit`,
   `sourceFullFrameOrientedGramCoord_mem_hypersurface`, and
   `sourceFullFrameOrientedGramVarietyCoord_subset_hypersurface`.
   The tangent target has also been algebraically identified as the
   symmetric-coordinate kernel by
   `mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_deriv_eq_zero`.
   Lean implementation checkpoint, 2026-05-03: the first derivative pass is
   now checked in
   `BHWPermutation/SourceOrientedFullFrameDerivative.lean`.  It adds
   `contDiff_sourceFullFrameOrientedEquation`,
   `differentiable_sourceFullFrameOrientedEquation`,
   `sourceFullFrameOrientedEquation_hasFDerivAt`,
   `sourceFullFrameOrientedEquation_hasDerivAt_detLine`,
   `sourceFullFrameOrientedEquation_fderiv_detDirection`,
   `sourceFullFrameOrientedEquation_fderiv_detDirection_ne_zero`,
   `sourceFullFrameOrientedEquation_fderiv_surjective_of_det_ne_zero`,
   `sourceFullFrameOrientedEquation_fderiv_surjectiveOnSymmetric_of_det_ne_zero`,
   `RegularZeroLocusAt`, `RegularZeroLocusInSubmoduleAt`, and the
   noncomputable regularity data
   `sourceFullFrameOrientedHypersurface_regularAt` and
   `sourceFullFrameOrientedHypersurface_regularInSymmetricAt`.  The
   regular-zero-locus theorem does **not** need the full Jacobi
   trace formula: it is enough to prove the actual Frechet derivative of
   `sourceFullFrameOrientedEquation d` is nonzero in the determinant
   coordinate direction.  The checked proof is
   mechanical: the determinant part is smooth by expanding `Matrix.det` as a
   finite sum of products of coordinate projections; the second coordinate is
   smooth by `contDiff_snd`.
   For the line
   `t ↦ H0.toCoord + t • sourceFullFrameDetDirection d`, the Gram coordinate
   is constant and the determinant coordinate is `H0.det + t`, so
   `HasDerivAt.pow` gives derivative
   `-((2 : ℂ) * minkowskiMetricDet d * H0.det)` at `0`.  Composing the
   actual `HasFDerivAt` of `sourceFullFrameOrientedEquation d` with this line
   and using uniqueness of one-variable derivatives identifies
   `(fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
     (sourceFullFrameDetDirection d)` with that nonzero scalar.  Surjectivity
   follows by scaling the determinant direction; the symmetric version uses
   `sourceFullFrameSymmetricDetDirection d`.

   Lean implementation checkpoint, 2026-05-03: the algebraic orbit-kernel
   half is now checked in `BHWPermutation/SourceOrientedFullFrameOrbit.lean`
   as `sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent`.  The
   proof writes any kernel vector as `X = M0 * (M0⁻¹ * X)`, conjugates the
   zero Gram-variation equation by `M0⁻¹` and `(M0ᵀ)⁻¹`, reads off
   `B η + η Bᵀ = 0`, extracts the determinant-coordinate equation
   `trace B = 0`, and packages `Bᵀ` as an element of
   `specialComplexLorentzLieAlgebra d`.  The reverse inclusion is the same
   calculation forward from `Aᵀ η + η A = 0` and `trace A = 0`.

   The same file now also checks the trace identity and the range-subset
   theorem:

   ```lean
   theorem BHW.sourceFullFrameOrientedDifferential_trace_identity
       (d : ℕ)
       {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
       (hM0 : IsUnit M0.det)
       (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
       Matrix.trace
           ((Matrix.of (BHW.sourceFullFrameGram d M0))⁻¹ *
             (Matrix.of
               (BHW.sourceFullFrameOrientedDifferential d M0 X).1)) =
         (2 : ℂ) * Matrix.trace (M0⁻¹ * X)
   ```

   The proof is pure matrix algebra: use
   `sourceFullFrameGram_eq_mul_eta_transpose`, invert
   `M0 * η * M0ᵀ` as `(M0ᵀ)⁻¹ * η * M0⁻¹`, rewrite the two summands under
   the trace to `M0⁻¹ * X` and its transpose using
   `Matrix.trace_mul_cycle`, and finish with `Matrix.trace_transpose`.
   It feeds the checked
   `sourceFullFrameOrientedDifferential_range_subset_tangent`.

   The range target is now checked constructively, without a rank-nullity
   detour.  For
   `Y ∈ sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)`,
   set
   `G := Matrix.of Y.1` and
   `B := (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
     ComplexLorentzGroup.ηℂ (d := d))`, and take the preimage
   `X := M0 * B`.  The theorem
   `sourceFullFrameOrientedDifferential_constructedGram` proves the Gram
   component by using `η² = 1`, `Gᵀ = G`, and the two inverse identities for
   `M0` and `M0ᵀ`.  The theorem
   `sourceFullFrameOrientedDifferential_constructedDet` proves the determinant
   component by applying the checked trace identity to `X = M0 * B`, rewriting
   the tangent equation with `sourceFullFrameGram_det_eq`, and cancelling
   `(2 : ℂ)`, `minkowskiMetricDet d`, and `M0.det`.  Thus
   `sourceFullFrameOrientedDifferential_range_eq_tangent` is checked in
   `BHWPermutation/SourceOrientedFullFrameOrbit.lean`.
   The same file now checks the gauge-slice linear algebra as
   data-valued definitions/theorems:
   `sourceFullFrameGaugeSlice_exists` is a noncomputable definition, choosing
   a complement by `Submodule.exists_isCompl`, restricting the checked
   differential to that complement, and proving bijectivity by
   `sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent` plus
   `sourceFullFrameOrientedDifferential_range_eq_tangent`;
   `sourceFullFrameSlice_differential_linearEquiv` exposes the stored linear
   equivalence; and
   `sourceFullFrameSlice_restricted_range_eq_tangent` proves the range of the
   restricted differential is exactly the oriented tangent space.
   `contDiff_sourceFullFrameGaugeSliceMap` proves the gauge-slice map is
   holomorphic by composing the affine translation from the slice with the
   already checked `contDiff_sourceFullFrameOrientedGramCoord`.  The
   producer is intentionally a `noncomputable def`, not a theorem returning
   data, because the complement is chosen from an existence proposition.
   Lean implementation checkpoint, 2026-05-03: the full Jacobi/Frechet packet
   is now checked in `BHWPermutation/SourceOrientedFullFrameJacobi.lean`.
   The checked determinant spine is
   `matrix_det_hasFDerivAt_expansion`,
   `matrix_det_one_add_hasDerivAt_trace`,
   `matrix_det_one_hasFDerivAt_trace`,
   `matrix_det_hasFDerivAt_trace`, and
   `sourceFullFrameDet_hasFDerivAt`; it proves Jacobi's formula by
   differentiating the Leibniz determinant expansion, reducing the identity
   case to Mathlib's polynomial theorem
   `Matrix.derivative_det_one_add_X_smul`, and transporting from `1` to an
   invertible `M0` by left multiplication with `M0⁻¹`.  The checked Gram spine
   remains `sourceFullFrameTransposeCLM`,
   `sourceFullFrameGramDifferentialCLM`,
   `sourceFullFrameTranspose_hasFDerivAt`,
   `sourceFullFrameGramMatrix_hasFDerivAt`, and
   `sourceFullFrameGram_hasFDerivAt`, using `HasFDerivAt.mul'` for the
   noncommutative product `M η Mᵀ`.  These assemble as the checked theorem
   `sourceFullFrameOrientedGram_hasFDerivAt`.
   The same file also closes the regular-zero-locus tangent mismatch by
   proving `sourceFullFrameOrientedEquation_hasFDerivAt_trace`, the actual
   Frechet derivative of
   `det gram - minkowskiMetricDet d * det^2` in trace form, and
   `mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_fderiv_eq_zero`,
   identifying the oriented tangent space with the kernel of the actual
   `fderiv` inside symmetric coordinates.
   The same file now checks the slice derivative bridge:
   `sourceFullFrameGaugeSliceMap_zero`,
   `sourceFullFrameGaugeSliceMap_mem_varietyCoord`,
   `sourceFullFrameGaugeSliceMap_mem_hypersurface`,
   `sourceFullFrameGaugeSliceMap_hasFDerivAt`,
   `sourceFullFrameGaugeSliceMap_hasStrictFDerivAt`,
   `sourceFullFrameGaugeSliceMap_fderiv_eq`,
   `sourceFullFrameGaugeSliceMap_fderiv_range_eq_tangent`, and
   `sourceFullFrameGaugeSliceMap_fderiv_kernel_eq_bot`.  Thus the next
   unimplemented full-frame target is no longer a derivative calculation.
   Lean implementation checkpoint, 2026-05-03: the next local-image support
   layer is checked in
   `BHWPermutation/SourceOrientedFullFrameLocalImage.lean`.  It defines the
   symmetric restricted equation
   `sourceFullFrameSymmetricEquation`, its actual derivative
   `sourceFullFrameSymmetricEquationDerivCLM`, and the base point
   `sourceFullFrameSymmetricBase`; proves
   `sourceFullFrameSymmetricEquation_hasFDerivAt`,
   `sourceFullFrameSymmetricEquation_hasStrictFDerivAt`, and
   `sourceFullFrameSymmetricEquationDerivCLM_range_eq_top_of_det_ne_zero`;
   and constructs the Mathlib IFT chart
   `sourceFullFrameSymmetricEquation_implicitChart`.  It also names the exact
   gauge-slice derivative maps into the IFT chart target:
   `sourceFullFrameGaugeSliceSymmetricDerivCLM` and
   `sourceFullFrameGaugeSliceKernelDerivCLM`.  The remaining
   full-frame local-image target is to compare this implicit hypersurface
   chart with the checked gauge-slice map, yielding
   `sourceFullFrameSlice_localImage_eq_hypersurface`, then restrict to
   `sourceFullFrameSlice_localImage_eq_variety`.
   The comparison is now fixed at Lean-pseudocode level as follows.  First
   define the nonlinear slice map with codomain already restricted to
   symmetric coordinates:
   `sourceFullFrameGaugeSliceMapSymmetric d M0 S X :=
   ⟨sourceFullFrameGaugeSliceMap d M0 S X,
   (sourceFullFrameGaugeSliceMap_mem_hypersurface d M0 S X).1⟩`.
   Prove its zero value, hypersurface equation, and strict derivative at
   `0` by composing `sourceFullFrameGaugeSliceMap_hasStrictFDerivAt` with the
   symmetric-subtype embedding and then proving the restricted derivative by
   extensionality after applying the subtype projection, with derivative
   `sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0 S`.
   Next expose
   `sourceFullFrameGaugeSliceKernelDerivLinearEquiv`: injectivity is
   proved by coercing an equality in the kernel codomain to symmetric
   coordinates, then to ambient oriented coordinates, and applying the already
   checked kernel theorem
   `sourceFullFrameGaugeSliceMap_fderiv_kernel_eq_bot`; surjectivity sends a
   kernel vector `K` to the tangent space using
   `mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_fderiv_eq_zero`,
   then uses
   `sourceFullFrameGaugeSliceMap_fderiv_range_eq_tangent` to choose the slice
   preimage.  This avoids doing subtraction inside the kernel subtype, which
   triggers typeclass-heartbeat issues, and keeps the proof in ambient
   coordinates.

   With the linear equivalence in hand, define the nonlinear kernel-coordinate
   map
   `sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S X :=
   ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
     (sourceFullFrameGaugeSliceMapSymmetric d M0 S X)).2`.
   At `X = 0`, Mathlib's theorem
   `HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self`, together with
   `sourceFullFrameGaugeSliceMap_zero` and
   `sourceFullFrameOrientedEquation d (sourceFullFrameOrientedGramCoord d M0)
   = 0`, gives value `0`.  The derivative is obtained by the identity
   theorem for the implicit chart on kernel directions,
   `implicitToOpenPartialHomeomorph_apply_ker`, applied to
   `sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S X` and the base point
   `sourceFullFrameSymmetricBase d M0`, plus a first-order expansion of
   `sourceFullFrameGaugeSliceMapSymmetric` with the checked strict derivative.
   Equivalently, and preferably in Lean, use
   `HasStrictFDerivAt.to_local_left_inverse` on the implicit chart's local
   inverse `implicitFunction` and compose with the strict derivative of the
   slice map; the resulting derivative of the second coordinate is exactly
   `sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S`.  Finally apply
   Mathlib's inverse-function theorem to this kernel-coordinate map through
   `sourceFullFrameGaugeSliceKernelDerivLinearEquiv`; the continuous-linear
   upgrade is a finite-dimensional API conversion when the inverse-function
   theorem is applied.  The target
   neighborhood in the kernel coordinate chart is then pulled back by the
   implicit chart inverse with first coordinate `0`, giving
   `sourceFullFrameSlice_localImage_eq_hypersurface`; restriction to the
   actual image variety uses only
   `sourceFullFrameGaugeSliceMap_mem_varietyCoord` and
   `sourceFullFrameOrientedGramVarietyCoord_subset_hypersurface`.
   Lean implementation checkpoint, 2026-05-03: the first half of this
   comparison is checked.  `SourceOrientedFullFrameLocalImage.lean` now adds
   the generic codomain-restriction helper
   `hasStrictFDerivAt_submodule_codRestrict`,
   `sourceFullFrameGaugeSliceMapSymmetric`,
   `sourceFullFrameGaugeSliceMapSymmetric_zero`,
   `sourceFullFrameGaugeSliceMapSymmetric_hasStrictFDerivAt`,
   `sourceFullFrameGaugeSliceKernelDerivCLM_ker_eq_bot`,
   `sourceFullFrameGaugeSliceKernelDerivCLM_range_eq_top`,
   `sourceFullFrameGaugeSliceKernelDerivLinearEquiv`,
   `sourceFullFrameSymmetricEquationKernelProjection`,
   `sourceFullFrameSymmetricEquationKernelProjection_apply_ker`,
   `sourceFullFrameSymmetricEquation_implicitChart_snd`,
   `sourceFullFrameGaugeSliceImplicitKernelMap`,
   `sourceFullFrameGaugeSliceImplicitKernelMap_zero`, and
   `sourceFullFrameGaugeSliceImplicitKernelMap_hasStrictFDerivAt`,
   `sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv`,
   `sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe`,
   `sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph`, and
   `sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe`,
   `sourceFullFrameGaugeSliceImplicitKernelMap_surjOn_chartTarget`,
   `sourceFullFrameGaugeSliceImplicitKernelMap_right_inv_on_chartTarget`, and
   `sourceFullFrameGaugeSliceImplicitKernelMap_left_inv_on_chartSource`.  The
   checked
   proof of the symmetric strict derivative is the generic submodule codomain
   restriction of the already checked ambient strict derivative.  The checked
   proof of surjectivity is the intended ambient-coordinate proof: a kernel
   vector is converted to the full-frame tangent space by
   `mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_fderiv_eq_zero`
   and then lifted from the range theorem
   `sourceFullFrameGaugeSliceMap_fderiv_range_eq_tangent`.  The checked
   derivative of the implicit kernel map is the literal projection transcript:
   Mathlib's implicit chart has second coordinate
   `sourceFullFrameSymmetricEquationKernelProjection d M0
   (H - sourceFullFrameSymmetricBase d M0)`, the projection is the identity on
   the kernel, and composition with the checked symmetric slice derivative gives
   exactly `sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S`.  The next Lean
   checked inverse-function step upgrades the checked linear equivalence to a
   continuous linear equivalence by keeping the forward continuous-linear map
   and proving inverse continuity as finite-dimensional linear-map continuity;
   `HasStrictFDerivAt.toOpenPartialHomeomorph` then gives the checked local
   chart.  Lean implementation checkpoint, 2026-05-04:
   `SourceOrientedFullFrameTransport.lean` now records the first exported
   transport consumer:
   `sourceFullFrameSymmetricHypersurfaceCoord`,
   `sourceFullFrameGaugeSliceMapSymmetric_mem_hypersurface`, and
   `sourceFullFrameGaugeSliceImplicitKernel_target_lifts_to_hypersurface`.
   Thus every kernel coordinate in the checked open-partial-homeomorphism
   target is realized by an actual gauge-slice point on the symmetric
   hypersurface, with prescribed kernel projection coordinate
   `sourceFullFrameSymmetricEquationKernelProjection d M0
   (H - sourceFullFrameSymmetricBase d M0)`.  Lean implementation checkpoint,
   2026-05-04: the neighborhood-at-zero strengthening is now checked in
   `SourceOrientedFullFrameLocalImage.lean` as
   `sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource`,
   `sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartTarget`,
   `sourceFullFrameGaugeSliceImplicitKernel_chartSource_mem_nhds_zero`, and
   `sourceFullFrameGaugeSliceImplicitKernel_chartTarget_mem_nhds_zero`.  The
   exported transport theorem
   `sourceFullFrameGaugeSliceImplicitKernel_eventually_lifts_to_hypersurface`
   now says that every sufficiently small kernel coordinate is realized by a
   gauge-slice point on the symmetric full-frame hypersurface, with the exact
   kernel-projection coordinate.  The restriction from the symmetric
   hypersurface statement to the actual full-frame source variety is now
   checked in `SourceOrientedFullFrameTransport.lean` as
   `sourceFullFrameSymmetricVarietyCoord`,
   `sourceFullFrameGaugeSliceMapSymmetric_mem_varietyCoord`,
   `sourceFullFrameGaugeSliceImplicitKernel_target_lifts_to_varietyCoord`, and
   `sourceFullFrameGaugeSliceImplicitKernel_eventually_lifts_to_varietyCoord`.
   The proof is deliberately not another analytic theorem: the gauge-slice map
   is by definition an image point of `sourceFullFrameOrientedGramVarietyCoord`,
   and the checked kernel-chart right inverse supplies the prescribed kernel
   coordinate.  Lean implementation checkpoint, 2026-05-04: the
   determinant-nonzero shrink is now checked in the same file as
   `sourceFullFrameSymmetricDetNonzeroCoord`,
   `sourceFullFrameSymmetricDetNonzeroCoord_open`,
   `sourceFullFrameSymmetricBase_mem_detNonzeroCoord`,
   `sourceFullFrameGaugeSliceMapSymmetric_detNonzero_mem_nhds_zero`,
   `sourceFullFrameGaugeSliceImplicitKernel_symm_detNonzero_mem_nhds_zero`,
   and
   `sourceFullFrameGaugeSliceImplicitKernel_eventually_lifts_to_detNonzero_varietyCoord`.
   This proves that, after shrinking near the zero kernel coordinate, the lifted
   gauge-slice point lies on the actual full-frame variety and still has
   nonzero selected determinant.  Lean implementation checkpoint, 2026-05-04:
   `SourceOrientedFullFrameChart.lean` now starts the max-rank chart packet
   with checked definitions and topology for `sourceComplementIndex`,
   `sourceSelectedMixedRows`, `continuous_sourceSelectedMixedRows`,
   `sourceFullFrameSelectedDetNonzeroDomain`,
   `sourceFullFrameSelectedDetNonzeroDomain_open`,
   `sourceFullFrameSelectedSymmetricCoordOfSource`,
   `sourceFullFrameSelectedSymmetricCoordOfSource_mem_varietyCoord`, and
   `sourceFullFrameSelectedSymmetricCoordOfSource_mem_detNonzeroCoord`.  These
   are the finite mixed-row and selected-coordinate inputs for the local product
   chart.  Lean implementation checkpoint, 2026-05-04: the selected
   kernel-coordinate and first reconstruction layer are now checked in
   `SourceOrientedFullFrameChart.lean`:
   `sourceFullFrameSelectedKernelCoord`,
   `sourceFullFrameSelectedKernelCoord_eq_kernelProjection`,
   `sourceFullFrameSelectedKernelCoord_eq_zero_of_selected_eq_base`,
   `sourceSelectedIndexOfMem`, `sourceSelectedIndexOfMem_spec`,
   `sourceFullFrameGauge_reconstructFrame`,
   `sourceFullFrameGauge_reconstructVector`, and
   `sourceFullFrameGauge_reconstructVector_selected`.  Lean implementation
   checkpoint, 2026-05-04: `sourceFullFrameGauge_reconstructVector_mixedGram`
   is also checked.  It proves the unselected reconstructed rows have the
   prescribed mixed Gram coordinates by finite-dimensional cancellation
   `(row * A⁻¹) * A = row`, with
   `A = Matrix.of (sourceFullFrameGram d reconstructedFrame)`.  Lean
   implementation checkpoint, 2026-05-04: the generic coefficient-row algebra
   is checked as
   `sourceFullFrameGauge_reconstructCoeff`,
   `sourceFullFrameGauge_reconstructCoeff_selected`,
   `sourceFullFrameGauge_reconstructVector_eq_sum_coeff_frame`,
   `sourceFullFrameGauge_reconstructVector_gram_eq_coeff_gram`,
   `sourceFullFrameGauge_reconstructMatrix_eq_coeff_mul`, and
   `sourceFullFrameGauge_reconstructDet_eq_coeff_det_mul`.  The immediate
   coordinate-facing wrappers are also pinned: selected-selected Gram entries
   reduce to `sourceFullFrameGram d reconstructedFrame`, while the two mixed
   source-Gram orientations reduce to the free row `y.2 k a` by
   `sourceFullFrameGauge_reconstructVector_mixedGram` and symmetry of
   `sourceComplexMinkowskiInner`; in Lean these are checked as
   `sourceFullFrameGauge_reconstructVector_selectedSelectedGram`,
   `sourceFullFrameGauge_reconstructVector_mixedSourceGram_left`, and
   `sourceFullFrameGauge_reconstructVector_mixedSourceGram_right`.  The next Lean target is the oriented
   Schur/determinant recovery theorem connecting these coefficient formulas to
   the input `SourceOrientedGramData`, followed by the local-biholomorph packet.
   The rank-deficient half has also been tightened: the proof must build
   `SourceOrientedRankDeficientResidualChartData` before it may return
   `SourceOrientedRankDeficientRealizationData`.  This residual chart stores a
   compact closed parameter polydisc `K`, an open interior `P`, a continuous
   residual-frame vector formula `toVec`, surjectivity of the invariant map
   from `P` onto the nearby oriented variety, and max-rank density in
   parameters.  The quotient-value support is then split into
   `sourceOrientedQuotientValue_locallyBounded_of_residualChart` and
   `sourceOrientedQuotientValue_continuous_of_residualChart`.  Arbitrary
   choice of an extended-tube lift is now explicitly insufficient because it
   gives neither boundedness nor continuity.  The residual chart itself is
   now decomposed through Schur residual realization: the Euclidean tail model
   `SourceTailOrientedData`, `sourceTailOrientedInvariant`,
   `sourceTailOrientedVariety_eq_algebraic`, and
   `sourceTailOrientedSmallRealization` proves the finite constructive
   theorem, while the OS-source residual chart consumes only the shifted
   wrapper `SourceShiftedTailOrientedData`,
   `sourceShiftedTailOrientedInvariant`, and
   `sourceShiftedTailSmallRealization`,
   `SourceOrientedSchurResidualData`,
   `sourceOriented_schurResidualData_of_tail_mem` fed by
   `sourceOrientedSchurResidualTailData_mem_variety`, and the checked endpoint
   `sourceOriented_reconstruct_from_schurResidual`.  The small tail theorem
   is proved constructively by quantitative Takagi same-Gram factorization
   plus determinant-sheet repair/vanishing; it does not scale an arbitrary
   realizing tuple, because scaling changes the prescribed Gram and determinant
   coordinates.  The local-image consumer should not require a single-radius
   compatible-box theorem at this layer.  It uses the one-way shifted
   realization for Schur image-surjectivity, while the forward inclusion of a
   small parameter box into the ambient Schur neighborhood is supplied
   separately by continuity/polynomial shrink estimates for the normal
   parameter map.  The blueprint now exposes the checked Euclidean
   small-realization
   cases:
   `sourceTailOrientedSmallRealization_zeroGram`,
   `sourceTailFullFrame_factorWithDet`,
   `sourceTailOrientedSmallRealization_fullRankStep`,
   `sourceTailOrientedSmallRealization_fullRank_bound`,
   `sourceTailOrientedSmallRealization_rankLt_bound`, and
   `sourceTailOrientedSmallRealization`, with an explicit
   positive-tail-dimension hypothesis `0 < D`.  The earlier intermediate
   Schur recursion is no longer an active Euclidean-tail blocker after the
   global quantitative Takagi theorem: if `sourceGramMatrixRank m T.gram < D`,
   every full `D × D` determinant coordinate of a tail-variety point is forced
   to vanish by `sourceTailOrientedVariety_selectedGram_det` and
   `sourceMatrix_minors_eq_zero_of_rank_le`.  Thus a small same-Gram factor
   already realizes the full oriented datum in the rank-deficient branch.
   Tail source permutations remain explicit through
   `sourceTailPermuteOrientedData`, `sourceTailOrientedInvariant_perm`,
   `sourceTailOrientedVariety_perm_iff`, and
   `sourceTailSmallRealization_transport_perm`, so determinant coordinates
   move by ordered-embedding composition with no hidden sign.  This avoids an
   implementation-level hole where "selected rank" was named but no
   invertible block was available to invert.  The full-rank tail case is no
   longer hidden inside the Schur recursion: after choosing
   `ι : Fin D ↪ Fin m`, use it only to fix the determinant sheet.  The
   determinant-orientation core is checked as
   `sourceTailFullFrame_factorWithDet`, but the active full-rank realization
   no longer needs a separate quantitative selected-block theorem: the checked
   `SourceOrientedTailSmallRealization.lean` route factors the entire
   rank-`D` Gram matrix by `sourceComplexSymmetric_factorSmall_rankLE` and
   then repairs the selected determinant by reflection.  The equality
   `det(A) = (T.det ι)^2` remains exposed for arbitrary tail-variety points as
   `sourceTailOrientedVariety_selectedGram_det`, not reproved from a hidden
   witness in the full-rank step.  The full-rank realization route should
   factor the entire small rank-`D` Gram matrix, not solve remaining rows by
   inverse coefficients: after obtaining a small factor `q0` with the same
   Gram, compare `det(q0 ∘ ι)` with `T.det ι`; if the sign is wrong, apply
   the checked coordinate reflection `sourceTailOrientedInvariant_reflection`,
   whose norm preservation is `sourceTail_reflection_norm`.  Once the
   selected determinant matches, all determinant coordinates follow from
   `sourceTailOrientedVariety_mixedGram_det` for `T` and
   `sourceTailOrientedInvariant_mixedGram_det` for the factor, canceling the
   nonzero selected determinant.  The assembled sign-repair consumer is
   checked as
   `sourceTailOrientedInvariant_or_reflection_eq_of_gram_eq`, and the
   quantitative small same-Gram factorization theorem is now checked as
   `sourceComplexSymmetric_factorSmall_rankLE`; together they prove
   `sourceTailOrientedSmallRealization_fullRankStep` and
   `sourceTailOrientedSmallRealization_fullRank_bound`.  This is a genuine top-rank branch, not an arbitrary
   Gram-factorization shortcut, and it avoids unstable inverse estimates in
   small blocks.
   The Schur reconstruction endpoint is also checked separately as
   `sourceOriented_reconstruct_from_schurResidual` and
   `exists_sourceOriented_reconstruct_from_schurResidual`: once
   `SourceOrientedSchurResidualData` exists and its shifted tail is realized,
   the hard-range Schur propagation theorem reconstructs the original
   oriented datum.  The head-gauge interface is now checked in
   `SourceOrientedHeadGauge.lean`: the symmetric head block is bundled only
   after the hypothesis `G ∈ sourceOrientedGramVariety d n`, and
   `sourceOriented_schurResidualData_of_tail_mem` proves that a local
   signature-relative head factor plus membership of the explicit residual
   tail datum in the shifted-tail variety mechanically constructs
   `SourceOrientedSchurResidualData`.  The explicit residual-tail membership
   theorem is now checked in `SourceOrientedHeadGaugeNormal.lean` as
   `sourceOrientedSchurResidualTailData_mem_variety`, and the full residual
   packet producer is checked as
   `sourceOriented_schurResidualData_of_headGauge`.  The remaining producer
   work around this interface is therefore the analytic inverse-function
   producer `sourceRankDeficientHeadGauge_at_sourceMetric` and the local radius
   choices needed to feed the residual chart.  The checked companion
   `SourceOrientedHeadGaugeSupport.lean` now also specializes the Schur
   determinant propagation theorem to the head-gauge interface:
   `sourceHeadRows_linearIndependent_of_headGauge` gives actual head-row
   independence for a realizing source tuple,
   `exists_headTail_fullFrameDet_ne_zero_of_headGauge_maxRank` gives the
   max-rank nonzero selected head-tail determinant, and
   `sourceOrientedGramData_eq_of_gram_eq_headTailDet_eq_of_headGauge` reduces
   future normal-form comparison to ordinary Gram equality plus the selected
   head-tail determinant coordinates.  This is the precise finite-dimensional
   consumer that the local Witt/head-normalizing producer now feeds through
   the checked residual-tail theorem.  The next checked
   interface is `SourceOrientedHeadGaugeNormal.lean`: it defines
   `SourceOrientedHeadGaugeNormalParameterData`, storing a normal-parameter
   representative `p` with
   `G = sourceOrientedMinkowskiInvariant (sourceOrientedNormalParameterVector p)`
   and with `p.head` exactly the head-gauge factor of the selected Schur head
   block.  From this data, `residualTail_mem_variety` and
   `schurResidualData` are now mechanical.  The bridge
   `sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized` is also
   checked: if a future proof supplies a realizing tuple `z`, a proper
   complex Lorentz transformation `Λ`, and pointwise equality
   `complexLorentzAction Λ z = sourceOrientedNormalParameterVector p`, then
   the normal-parameter data follows immediately by
   `sourceOrientedMinkowskiInvariant_complexLorentzAction`.  The same file now
   also checks the head-frame inputs to Witt: `sourceOrientedHeadGaugeHeadParameter`
   defines the gauge-head-only normal parameter,
   `sourceOriented_headGauge_actualHeadGram_eq_normalHeadGram` proves equality
   of the actual selected head Gram with the gauge normal-head Gram, and
   `sourceOriented_headGauge_normalHead_linearIndependent` proves linear
   independence of that gauge head frame.  The checked packet
   `SourceOrientedHeadGaugeFrameSameGramData` and constructor
   `sourceOriented_headGaugeFrameSameGramData` package precisely the
   finite-dimensional input to the checked Witt theorem: actual-head linear
   independence, normal-head linear independence, same Gram, and invertibility
   of the selected head Gram.  The next algebraic layer is also
   checked: `sourceVectorMinkowskiInner_right_hwLemma3CanonicalSource_head`
   extracts canonical head coordinates from pairings with the model head
   vectors,
   `sourceOriented_headGauge_headCoord_eq_zero_of_orthogonal_normalHead`
   proves that a vector orthogonal to the gauge normal head frame has zero
   canonical head coordinates,
   `eq_sourceTailEmbed_of_headCoord_eq_zero` identifies such a vector with its
   shifted-tail embedding, and
   `sourceOriented_headGaugeTailCoordinatesAfterWittData`/
   `sourceOriented_headGauge_tailCoordinates_after_witt` construct the Schur
   mixed coefficients plus shifted-tail coordinates once a Lorentz
   transformation has normalized the selected head frame.  Consequently
   `sourceOriented_headGaugeNormalParameterData_of_lorentz_head_normalized`
   is checked: once head-frame normalization is supplied, the normal-parameter
   data is assembled constructively.  The blockwise constructor
   `sourceOriented_headGaugeNormalParameterData_of_lorentz_head_tail` is
   checked as well, so future Lean can prove head and tail normalized
   equalities separately and assemble the data by the checked head/tail source
   split.  The typed output of the Witt theorem is now checked as
   `SourceOrientedHeadGaugeWittData`, with checked producer
   `sourceOriented_headGaugeWittData` and checked consumer
   `SourceOrientedHeadGaugeWittData.normalParameterData`; this avoids the
   invalid pattern of extracting a Lorentz witness from a Prop-valued
   existential to build Type-valued tail-coordinate data.  The determinant-one
   Witt/head-normalization producer for that data is now checked as the
   Type-valued `complexMinkowski_detOneWittExtension_to_headFactorFrame`.
   Its proof normalizes the actual head frame by the checked head factor `H`,
   uses the checked signed `SOComplex` prefix-frame transitivity and Wick
   transport to reach the canonical head frame, then recomposes through `H`
   to reach the gauge normal head frame.  The fully assembled
   `sourceOriented_headGaugeNormalParameterData`,
   `sourceOrientedSchurResidualTailData_mem_variety`, and
   `sourceOriented_schurResidualData_of_headGauge` are now checked as well.
   The stabilizer support needed for the induction is now checked and public
   in `SOConnected.lean`: `SOComplex.embed_val_zero_zero`,
   `SOComplex.embed_val_zero_succ`, `SOComplex.embed_val_succ_zero`,
   `SOComplex.embed_val_succ_succ`, `SOComplex.embed_mulVec_zero`,
   `SOComplex.embed_mulVec_succ`, and `SOComplex.of_first_col_e0`.  The
   signed one-column step is checked as `SOComplex.exists_so_with_firstCol_of_sq`:
   a vector of square norm `σ ^ 2` with `σ ≠ 0` is the `σ`-multiple of the
   first column of an `SOComplex` element.  The one-column descent algebra is
   now also checked in `SOFrameTransitivity.lean`:
   `SOComplex.inv_mulVec_zero_eq_sum_col`,
   `SOComplex.inv_mulVec_zero_eq_zero_of_signed_col_orth`,
   `SOComplex.dot_mulVec_eq`, `SOComplex.sumSq_mulVec_eq`,
   `SOComplex.mulVec_inv_mulVec`, `SOComplex.inv_mulVec_mulVec`,
   `SOComplex.sum_tail_sq_eq_of_zero_head`,
   `SOComplex.sum_tail_mul_eq_of_zero_heads`,
   `SOComplex.tail_sq_eq_of_inv_mulVec_signed_col_orth`,
   `SOComplex.tail_dot_eq_of_inv_mulVec_signed_col_orth`,
   `SOComplex.mul_embed_val_col_zero`, and
   `SOComplex.mul_embed_val_col_succ`.  These lemmas give the exact induction
   step for signed prefix frames: choose `A₀` with first column `v₀ / σ₀`;
   every remaining frame vector has zero first coordinate after `A₀⁻¹`
   because it is orthogonal to `v₀`; dropping that coordinate preserves all
   remaining square norms and pairwise dot products; recursively normalize the
   tail frame by `B`; and assemble the ambient matrix as `A₀ * SOComplex.embed B`.
   The two checked `mul_embed` lemmas prove the first column is still `A₀`'s
   first column and the later columns are exactly `A₀` applied to the embedded
   normalized tail columns.  The induction theorem packaging this transcript is
   now checked as `SOComplex.exists_so_with_signedPrefixCols`.
   The forward normal-parameter check is
   now also in Lean:
   `sourceOrientedSchurResidualTailData_normalParameter` identifies the
   explicit residual tail datum of a normal-parameter invariant with
   `sourceShiftedTailOrientedInvariant p.tail`, and
   `sourceOrientedSchurResidualTailData_normalParameter_mem_variety` gives the
   corresponding shifted-tail-variety membership.  The equality-transport
   bridge `sourceOrientedSchurResidualTailData_mem_variety_of_eq_normalParameter`
   is also checked, and the all-variety membership theorem now extends this
   calculation through the checked local head-gauge normal form rather than
   redefining the residual tail.
   The final `sourceTailOrientedSmallRealization` theorem is now assembled by
   a two-way rank split, not a strong Schur induction.  The top-rank branch
   calls `sourceTailOrientedSmallRealization_fullRank_bound`; the lower-rank
   branch calls `sourceTailOrientedSmallRealization_rankLt_bound` after using
   `sourceTailOrientedVariety_rank_le` to turn `rank ≠ D` into `rank < D`.
   The determinant-smallness hypothesis remains in the public theorem surface
   for compatibility with the paired box producer, but the checked realization
   proof uses only Gram smallness plus the variety relations.
   The residual-chart producer is now split one layer further.  Before Lean
   may implement the extended-tube residual chart, the blueprint requires only
   genuine ambient transports where they are mathematically available, and uses
   the checked variety-relative transport interface for source-matrix normal
   forms.  The active no-tube algebraic producer is based on
   `SourceOrientedRankDeficientAlgebraicNormalFormData` and
   `SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint`;
   the older `SourceOrientedInvariantTransportEquiv` shortcut is not permitted
   for source changes.  The remaining extended-tube residual-chart surfaces are
   `SourceOrientedRankDeficientNormalFormData`,
   `SourceOrientedRankDeficientNormalFormData.exists_ofExtendedTube`,
   `SourceOrientedResidualPolydiscData`,
   `sourceOriented_rankDeficient_tubeResidualPolydisc`, and
   `SourceOrientedRankDeficientTubeResidualPolydiscProducer`.  These surfaces force the
   ordinary Hall-Wightman adapted normal form, the residual coefficient
   polydisc, the extended-tube stability shrink, Schur-tail image
   surjectivity, and max-rank density to be proved before the residual chart
   can be assembled.  The checked transport interfaces in
   `SourceOrientedTransport.lean` are still useful, but the residual-chart
   producer may not depend on an ambient `SourceOrientedInvariantTransportEquiv`
   for source-matrix normal forms.  The checked source-matrix return path is
   variety-relative (`SourceOrientedVarietyTransportEquiv`), so the
   extended-tube residual polydisc must return its original-coordinate ambient
   open set directly: `Ω : Set (SourceOrientedGramData d n)`,
   `Ω_open : IsOpen Ω`, original-coordinate image membership, original-coordinate
   image surjectivity, and original-coordinate max-rank density.  The ambient
   `Ω` is chosen after pulling the normal subtype-open Schur image back through
   the variety transport and representing that relatively open set by an
   actual ambient open neighborhood; it is not obtained by applying an
   unavailable ambient source-matrix coordinate homeomorphism.  The
   normal-form packet now separates the actual
   extended-tube adapted representative `adaptedBase` from the canonical
   normal coordinate source `normalBase = hwLemma3CanonicalSource d n r`.
   The latter supplies the signature-diagonal head block
   `sourceHeadMetric d r hrD` and zero tail, but is not asserted to lie in
   `ExtendedTube`.  Tube membership after inverse
   transport is stored only in
   `SourceOrientedResidualPolydiscData.toOriginal_residualVector_mem_ET`.
   This closes the previous gap where an arbitrary source-coordinate normal
   form was implicitly treated as tube-preserving or as an ambient oriented
   coordinate homeomorphism.  The residual data now also stores the
   original-coordinate neighborhood `Ω`, image-surjectivity field, and max-rank
   density field, produced by the explicit
   `sourceOriented_rankDeficient_tubeResidualPolydisc` theorem.  That theorem
   uses head-factor, mixed-coefficient, and tail residual-vector coordinates;
   it is not allowed to recover surjectivity later from an arbitrary compact
   parameter set.  Its first Lean support helpers are now exact:
   `BHW.SourceOrientedRankDeficientNormalFormData.toAlgebraicNormalFormData`
   builds the already checked algebraic normal-form packet from the tube
   packet by reusing `r`, `hrD`, `hrn`, and `varietyTransport`; the center
   equation follows from `N.toOriginal_oriented`, `N.normalBase_eq`, and
   `N.toOriginal_normalBase_invariant`.  The companion bridge
   `BHW.SourceOrientedRankDeficientNormalFormData.originalNormalVarietyPoint_eq_toOriginal`
   identifies the algebraic transported normal image with the actual
   original-coordinate invariant
   `sourceOrientedMinkowskiInvariant d n (N.toOriginal
   (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn p))`.
   The extended-tube compact shrink is now started by the checked helpers
   `BHW.SourceOrientedRankDeficientNormalFormData.toOriginal_normalParameterVector_center`,
   `BHW.SourceOrientedRankDeficientNormalFormData.continuous_toOriginal_normalParameterVector`,
   `BHW.SourceOrientedRankDeficientNormalFormData.toOriginal_normalParameterVector_mem_ET_mem_nhds_center`,
   and
   `BHW.SourceOrientedRankDeficientNormalFormData.exists_normalParameterBall_toOriginal_mem_ET`.
   These use `BHW.isOpen_extendedTube`,
   `BHW.continuous_sourceOrientedNormalParameterVector`, and
   `N.toOriginal_continuous`; they do not use any normal-form source change as
   a tube-preserving map.  The finite `Fin m -> ℂ` coordinate model for the
   eventual compact/open parameter pair is also checked in
   `SourceOrientedNormalParameterFinCoord.lean`, via
   `BHW.sourceOrientedNormalParameterFinCoordHomeomorph`,
   `BHW.isOpen_sourceOrientedNormalParameterFinCoordOpenBall`,
   `BHW.isCompact_sourceOrientedNormalParameterFinCoordClosedBall`, and
   `BHW.sourceOrientedNormalParameterFinCoordOpenBall_subset_closedBall`.
   The finite-coordinate neighborhood shrink is checked as
   `BHW.exists_sourceOrientedNormalParameterFinCoordClosedBall_subset_of_mem_nhds_center`.
   The tube-normal-form wrappers
   `BHW.SourceOrientedRankDeficientNormalFormData.exists_finCoordClosedBall_toOriginal_mem_ET`
   and
   `BHW.SourceOrientedRankDeficientNormalFormData.exists_finCoordCompactOpen_toOriginal_mem_ET`
   now produce the actual closed compact ball `K`, open ball `P`, center
   membership, `P ⊆ K`, and pointwise
   `N.toOriginal (normalVector (decode c)) ∈ ExtendedTube d n` field used by
   the full normal-coordinate compact-shrink bridge.  This is not yet the
   final residual-polydisc parameter chart, because the checked Schur
   local-image producer is sliced.  The corresponding sliced finite-coordinate
   model is now checked in
   `SourceOrientedSlicedNormalParameterFinCoord.lean`:
   `BHW.sourceOrientedSlicedNormalParameterFinCoordHomeomorph`,
   `BHW.sourceOrientedSlicedNormalParameterFinCoordOpenBall`,
   `BHW.sourceOrientedSlicedNormalParameterFinCoordClosedBall`,
   `BHW.exists_sourceOrientedSlicedNormalParameterFinCoordClosedBall_subset_of_mem_nhds_center`,
   `BHW.SourceOrientedRankDeficientNormalFormData.exists_slicedFinCoordCompactOpen_toOriginal_mem_ET`,
   `BHW.SourceOrientedRankDeficientNormalFormData.continuousOn_slicedFinCoord_normalParameterVector_closedBall`,
   `BHW.SourceOrientedRankDeficientNormalFormData.toOriginal_slicedNormalParameterVector_maxRank_iff_tail`,
   `BHW.isOpen_sourceOrientedSlicedNormalParameterFinCoord_image`,
   `BHW.sourceOrientedSlicedNormalParameterFinCenterCoord_mem_image`,
   `BHW.sourceOrientedSlicedNormalParameterFinCoord_image_subset_closedBall`,
   `BHW.SourceOrientedRankDeficientNormalFormData.slicedFinCoord_originalImage_mem_varietyTransport`,
   and
   `BHW.SourceOrientedRankDeficientNormalFormData.slicedFinCoord_originalImage_surj_varietyTransport`.
   The compact/open sliced Schur-window sandwich is now also checked:
   `BHW.exists_sourceMatrixCoordinateWindow_subset_of_mem_nhds`,
   `BHW.exists_sourceOrientedRankDeficientSlicedSchurParameterWindow_coordinate_bounds_subset_of_mem_nhds_center`,
   `BHW.exists_sourceOrientedRankDeficientSlicedSchurParameterWindow_subset_of_mem_nhds_center`,
   `BHW.SourceOrientedRankDeficientAlgebraicNormalFormData.exists_slicedSchurParameterWindow_subset_nhds_image_subset_open_headDomain_tailRank_connected`,
   `BHW.SourceOrientedRankDeficientNormalFormData.exists_slicedSchurWindow_finCoordControl`,
   and the hard-range constructor
   `BHW.sourceOriented_rankDeficient_tubeResidualPolydisc_hardRange`.
   The proof is formal from the checked head-slice symmetric-coordinate
   homeomorphism, finite-dimensional `ContinuousLinearEquiv.ofFinrankEq`,
   the existing sliced-to-normal forgetful continuity theorem, and
   `N.toOriginal_normalParameterVector_mem_ET_mem_nhds_center`, plus the
   checked variety-relative transport equality
   `N.originalNormalVarietyPoint_eq_toOriginal`.  The final residual-polydisc
   uses `residualVector c := normalVector ((decode c).toNormalParameter)`,
   with compact `K` supplied by the sliced extended-tube shrink and open `P`
   supplied by the sliced Schur image window after shrinking that window into
   `K`.  In the hard range `d + 1 ≤ n`, the original-coordinate
   `SourceOrientedResidualPolydiscData` assembly is now checked: it represents
   the transported subtype-open `Ωv` by an ambient open `Ω`, fills
   `Ω_center`, `originalInvariant_mem`, and `image_surj` using the checked
   sliced finite-coordinate variety-transport bridges, and fills
   `maxRank_dense_original` from
   `BHW.sourceOrientedMaxRank_dense_in_relOpen_inter` plus image-surjectivity.
   The public all-arity residual-polydisc theorem now splits before this call.
   The complementary `n < d + 1` branch is checked through:
   `BHW.sourceOrientedNormalParameterVector_realizes_schur_det_smallArity`,
   `BHW.sourceOrientedNormalParameterVector_realizes_schur_smallArity`,
   `BHW.sourceOriented_reconstruct_from_schurResidual_smallArity`,
   `BHW.sourceOrientedHeadSliceGaugeSchurExtractedImage_subset_slicedParameter_image_smallArity`,
   `BHW.sourceOrientedHeadSliceGaugeSchurWindowCanonicalImage_smallArity`,
   `BHW.SourceOrientedRankDeficientNormalFormData.exists_slicedSchurWindow_finCoordControl_smallArity`,
   `BHW.SourceOrientedRankDeficientNormalFormData.slicedSchurWindow_originalMaxRank_dense`,
   `BHW.sourceOriented_rankDeficient_tubeResidualPolydisc_smallArity`,
   `BHW.sourceOriented_rankDeficient_tubeResidualPolydisc`,
   `BHW.sourceOriented_rankDeficient_tubeResidualPolydiscProducer`, and
   `BHW.sourceOriented_rankDeficient_residualChartProducer`.
   The Schur reconstruction proof is determinant-vacuous: for
   `ι : Fin (d + 1) ↪ Fin n`, `Fintype.card_le_of_embedding ι` contradicts
   `n < d + 1`.  The compact/open shrink is the same sliced finite-coordinate
   ET shrink plus Schur coordinate-window basis as the hard-range proof, with
   no tail-rank-connectedness requirement.  The image-surjectivity field uses
   the small-arity canonical image theorem, and the density field uses the
   fixed-head/fixed-mixed shifted-tail parameter-density lift.  This branch is
   a separate pure-Gram residual chart with empty oriented determinant
   families; it must not fake a hard-range hypothesis.
   The all-arity rank bridge
   `BHW.sourceOrientedNormalParameterVector_maxRank_iff_tail` is also
   checked: on the invertible-head normal-parameter locus, max rank of the
   full oriented image is equivalent to max rank of the shifted residual-tail
   invariant.  The original-coordinate version needed by the tube producer is
   checked as
   `BHW.SourceOrientedRankDeficientNormalFormData.toOriginal_normalParameterVector_maxRank_iff_tail`.
   Its max-rank-density field is now pinned by the checked all-arity
   parameter-density theorem in `SourceOrientedShiftedTailDensity.lean`,
   then rewritten through the same normal-parameter image.  The file checks
   `BHW.sourceShiftedTailGram_rank_le_max`,
   `BHW.sourceShiftedTail_maxRank_of_selectedGram_det_ne_zero`, the canonical
   full-rank template determinant, the selected-minor line polynomial,
   `BHW.dense_compl_sourceShiftedTailSelectedGramLineRoots`, and
   `BHW.sourceShiftedTailOrientedMaxRank_dense_in_parameterOpen`.  The
   density proof is a finite polynomial-line argument: for each tail parameter `q`
   and open `P ∋ q`, choose the canonical shifted-tail full-rank template `τ`,
   form the line `q + t • (τ - q)`, take the determinant polynomial of one
   selected `min (d + 1 - r) m` Gram block of `sourceShiftedTailGram`, prove
   this polynomial is nonzero by evaluating at `t = 1`, and use density of the
   complement of the finite root set in `ℂ` to choose `t` with the line still
   in `P` and the selected Gram block nonzero.  The template's first
   `min (d + 1 - r) m` tail rows are the
   corresponding coordinate basis vectors, the selected shifted Gram block is
   diagonal with nonzero `MinkowskiSpace.metricSignature` entries, and the
   root-avoidance helper is proved from `Polynomial.rootSet_finite` and
   `Dense.diff_finite`.  The small-arity residual chart uses the checked parameter
   closure strengthening
   `BHW.sourceShiftedTailOrientedMaxRank_parameter_dense_in_open`, proved by
   the same line/root-avoidance argument but with closure target
   `{q' | q' ∈ P ∧ SourceShiftedTailOrientedMaxRankAt ...}` instead of the
   shifted-tail invariant image.  The downstream lift
   `BHW.SourceOrientedRankDeficientNormalFormData.slicedSchurWindow_originalMaxRank_dense`
   fixes the sliced head and mixed coordinates, applies that tail-parameter
   density inside the open tail fiber of the Schur window, converts tail
   max-rank to original-coordinate max-rank using
   `BHW.SourceOrientedRankDeficientNormalFormData.toOriginal_slicedNormalParameterVector_maxRank_iff_tail`,
   and pushes closure through the finite-coordinate homeomorphism and the
   continuous original invariant map.  This is all-arity support and does not
   use the hard-range-only ambient density theorem.
   The downstream compactness support is also explicit:
   Lean checkpoint: `SourceOrientedRankDeficientTubeResidual.lean` now checks
   this corrected interface as data, not as a hidden axiom.  It introduces
   `BHW.SourceOrientedRankDeficientNormalFormData` with an actual
   `toOriginal` map, `BHW.SourceOrientedResidualPolydiscData` with
   original-coordinate `Ω`, membership, surjectivity, and max-rank-density
   fields, and the mechanical reducer
   `BHW.sourceOrientedRankDeficientResidualChartProducer_of_tubeResidualPolydiscProducer`.
   The same file also checks
   `BHW.SourceOrientedRankDeficientNormalFormData.ofSourceMatrixLorentz`:
   given an adapted extended-tube base, an invertible source matrix `M`, and a
   complex Lorentz transform `Λ` with
   `complexLorentzAction Λ (sourceTupleLinearChange d n M adaptedBase) =
   hwLemma3CanonicalSource d n r`, the actual return map is
   `sourceTupleLinearChange d n M⁻¹ ∘ complexLorentzAction Λ⁻¹`, and its
   source-variety compatibility is proved through the checked
   `SourceOrientedVarietyTransportEquiv` for `M`.  It also checks
   `BHW.SourceOrientedRankDeficientNormalFormData.exists_ofAdaptedBase`,
   which packages the existing Schur normal-form source matrix construction
   and Lorentz/Witt normalization into an existential source-level
   normal-form packet once an adapted extended-tube base with strict
   source-rank deficiency is already supplied, and
   `BHW.SourceOrientedRankDeficientNormalFormData.exists_ofExtendedTube`,
   which now combines the checked adapted ET representative with the
   rank-deficient same-oriented-invariant conversion.  The remaining hard
   theorem is the tube-valued residual-polydisc producer; the checked reducer
   and normal-form producer prove that no ambient source-matrix invariant
   transport is needed after those fields are available.  The checked theorem
   `BHW.isConnected_sourcePrincipalSchur_varietyTransported_orientedMaxRank_preimage_of_eq`
   is the connectedness form to call once the normal-parameter vector has been
   packaged as a `BHW.SourceOrientedVariety d n` point, identified with the
   principal Schur graph on the parameter box, and pulled back by the checked
   source-matrix variety transport.  The older ambient theorem
   `BHW.isConnected_sourcePrincipalSchur_transported_orientedMaxRank_parameterSet`
   is reserved for genuine full-coordinate homeomorphisms, not for arbitrary
   source changes.
   `sourceOrientedResidualChart_compactBound`,
   `sourceOrientedResidualChart_quotient_eq_parameter`,
   `sourceOrientedQuotientValue_locallyBounded_of_residualChart`, and
   `sourceOrientedResidualChart_clusterValue` are checked in
   `SourceOrientedScalarRepresentative.lean`, along with the generic compact
   parameter helper `SCV.continuousWithinAt_of_compact_parameter_surjection`
   and its consumer
   `sourceOrientedQuotientValue_continuous_of_residualChart`, and the
   conditional global assembly
   `sourceOrientedQuotientValue_continuous_locallyBounded_of_maxRankLocal`.
   This closes a
   previous documentation gap where compactness and branch-law independence
   were described in prose but not pinned as Lean-sized theorem surfaces.
   The compactness support is now proof-script level and checked:
   `compactBound` is `R.K_compact.exists_bound_of_continuousOn` applied to
   `extendF F ∘ R.toVec`; `quotient_eq_parameter` is a direct call to
   `sourceOrientedQuotientValue_wellDefined`; local boundedness is
   `compactBound` plus `R.image_surj`; and continuity is factored through
   `SCV.continuousWithinAt_of_compact_parameter_surjection`.  That helper uses
   compact separation of the bad parameter set
   `K ∩ value ⁻¹' Vᶜ`: its image under the continuous parameter map is compact
   and closed, does not contain the base point by the cluster-value hypothesis,
   and therefore supplies a target neighborhood on which every local parameter
   representative has value in `V`.  It is not an unconstrained subnet or choice
   placeholder.  In the residual-chart
   application, `hy0U` is derived from the original `hz0` witness, equivalently
   the stored field `R.center_mem_ET`; the compact-parameter center only has to satisfy
   `R.toVec_c0_invariant`, not `R.toVec c0 = z0`.  The production
   ordering is pinned: `sourceOrientedQuotientValue` and
   `sourceOrientedQuotientValue_wellDefined` must appear before
   `sourceOrientedResidualChart_quotient_eq_parameter`, even though the
   latter is discussed inside the residual-chart packet.  The cluster-value
   lemma uses `R.center_mem_ET` directly and compares fibres by the oriented
   invariant equality; it does not try to identify the adapted residual
   center source tuple with the original `z0`.  The remaining
   `sourceOrientedQuotientValue_continuous_locallyBounded` work is now exactly
   the max-rank local representative producer; the rank-deficient continuity
   and boundedness branch is no longer a blocker.
   Low-rank same-Gram orientation is now explicit: not-max-rank gives
   `sourceGramMatrixRank < d+1`; every full-frame determinant then vanishes
   by the Gram-minor identity
   `det Gram[ι] = minkowskiMetricDet d * sourceFullFrameDet(ι)^2`; hence an
   adapted same-Gram representative has the same oriented invariant as the
   original source tuple.
   The auxiliary subset theorem
   `sourceOrientedExtendedTubeDomain_subset_variety` is now stated and proved
   definitionally by destructing the image witness.
   The global continuity/local-boundedness theorem
   `sourceOrientedQuotientValue_continuous_locallyBounded` is now pinned as a
   pointwise split over an image witness `G0 = sourceOrientedMinkowskiInvariant
   d n z0`: the max-rank branch uses
   `sourceOrientedQuotientValue_holomorphicOn_maxRank` plus the purely
   topological glue helpers
   `SCV.continuousWithinAt_of_local_eqOn_relNeighborhood` and
   `SCV.locallyBoundedAt_of_local_eqOn_relNeighborhood`; the exceptional
   branch uses the residual-chart continuity and compact-bound theorems.  This
   closes the former prose-only step between local sections/residual charts and
   the `ContinuousOn`/`LocallyBoundedOn` hypotheses needed by the normal
   Riemann theorem.  The two topological glue helpers are now checked Lean:
   continuity is
   `ContinuousOn.continuousAt` on the open chart, `nhdsWithin_le_nhds`,
   eventual membership in `Ω ∩ V`, and `Tendsto.congr'`; local boundedness
   chooses an open preimage of `Metric.ball (Ψ x) 1` and transfers the bound
   `‖Ψ y‖ <= ‖Ψ x‖ + 1` through the same `EqOn`.
   The oriented holomorphic descent is now fixed as a quotient construction
   plus the regular/removable-singularity split: `sourceOrientedQuotientValue`
   is defined from `extendF F` on an oriented invariant fibre,
   `sourceOrientedQuotientValue_wellDefined` is proved by the oriented branch
   law, max-rank holomorphy is obtained from an actual ambient holomorphic
   local section, and exceptional rank is handled by
   `sourceOrientedVariety_normal_riemannExtension`.  A local holomorphic
   section at every singular oriented quotient point is not a valid theorem
   surface.  This prevents the Lean implementation from inventing an unrelated
   ambient `Phi` and asserting branch equality only afterward.

   Current max-rank section boundary, 2026-05-07: ordinary local realization
   and full-frame chart continuity are not enough for the scalar descent
   theorem.  The max-rank local representative must expose an ambient open
   neighborhood `Ω`, an actual section `toVec : SourceOrientedGramData d n ->
   Fin n -> Fin (d + 1) -> ℂ`, `toVec_mem : toVec G ∈ ExtendedTube d n`
   on `Ω`, `toVec_right_inv` on `Ω ∩ sourceOrientedGramVariety d n`, and
   `toVec_holomorphic : DifferentiableOn ℂ toVec Ω`.  The full-frame branch
   must therefore prove differentiability of the explicit chart candidate
   `G ↦ SourceFullFrameMaxRankChartAmbientShrink.chartCandidate hM0 S G`, or
   equivalently of
   `G ↦ sourceFullFrameGauge_reconstructVector d n ι M0 S
     (SourceFullFrameMaxRankChartAmbientShrink.chartCandidate hM0 S G)`, on the
   ambient shrink `T.Ωamb`.  This is the missing implicit-inverse regularity
   theorem for
   `sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph.symm`
   composed with the selected-kernel coordinate; it is distinct from the
   already checked tube shrink and from
   `continuousOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero`.
   The small-arity branch must similarly use an arbitrary-complex-base
   selected zero-section for the ordinary source Gram map inside
   `ExtendedTube`; the existing real-base zero-section support is not, by
   itself, a section at an arbitrary extended-tube max-rank point.  The generic
   inverse-chart differentiability consumer
   `SCV.openPartialHomeomorph_symm_differentiableOn_of_hasFDerivAt` is now
   checked in `SourceOrientedHolomorphicSection.lean`: it packages the exact
   `OpenPartialHomeomorph.contDiffAt_symm` proof pattern needed once the
   full-frame and small-arity producers provide pointwise invertible
   derivatives and smoothness of their forward chart maps.

   Lean-ready max-rank holomorphic-section producer contract, 2026-05-07:
   the proof is now split into four explicit targets, and implementation must
   follow this order.  First, prove the mechanical coordinate facts
   `sourceFullFrameSelectedKernelCoordAmbient_eq_kernelProjection`,
   `differentiable_sourceFullFrameSelectedKernelCoordAmbient`, and
   `differentiable_sourceSelectedMixedRows`.  The first fact rewrites the
   selected kernel coordinate as
   `sourceFullFrameSymmetricEquationKernelProjection d M0
     (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G -
       sourceFullFrameSymmetricBase d M0)`, so this coordinate is a fixed
   linear projection of ambient source-oriented coordinates; it does not use
   differentiability of the symmetric implicit chart.  Second, prove the
   corresponding forward gauge-slice regularity facts
   `sourceFullFrameGaugeSliceImplicitKernelMap_eq_projection` and
   `contDiff_sourceFullFrameGaugeSliceImplicitKernelMap`, again by rewriting
   through `sourceFullFrameSymmetricEquation_implicitChart_snd` and the
   checked polynomial `contDiff_sourceFullFrameGaugeSliceMap`.  Third, produce
   the actual inverse-regular target shrink:

   ```lean
   structure BHW.SourceFullFrameImplicitKernelTargetRegularityData
       (d : Nat)
       {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
       (hM0 : IsUnit M0.det)
       (S : BHW.SourceFullFrameGaugeSliceData d M0) where
     D : Set ((BHW.sourceFullFrameSymmetricEquationDerivCLM d
          (BHW.sourceFullFrameOrientedGramCoord d M0)).ker)
     D_open : IsOpen D
     zero_mem : 0 ∈ D
     D_subset_target :
       D ⊆
         (BHW.sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
           d hM0 S).target
     has_deriv_equiv :
       ∀ K ∈ D,
         ∃ e' : S.slice ≃L[ℂ]
             (BHW.sourceFullFrameSymmetricEquationDerivCLM d
               (BHW.sourceFullFrameOrientedGramCoord d M0)).ker,
           HasFDerivAt
             (BHW.sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
               d hM0 S)
             (e' : S.slice →L[ℂ]
               (BHW.sourceFullFrameSymmetricEquationDerivCLM d
                 (BHW.sourceFullFrameOrientedGramCoord d M0)).ker)
             ((BHW.sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
               d hM0 S).symm K)
     forward_smooth :
       ∀ K ∈ D,
         ContDiffAt ℂ ⊤
           (BHW.sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
             d hM0 S)
           ((BHW.sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
             d hM0 S).symm K)
     symm_differentiableOn :
       DifferentiableOn ℂ
         (BHW.sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
           d hM0 S).symm D
   ```

   This data is not an axiom surface: `D` is the intersection of the existing
   local-homeomorphism target with the image of the source-side neighborhood
   where the Frechet derivative of
   `sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S` remains an invertible
   continuous-linear equivalence.  The proof uses continuity of the derivative
   from the polynomial/`ContDiff` formula and openness of the unit group in
   finite-dimensional continuous-linear maps, then invokes the checked helper
   `SCV.openPartialHomeomorph_symm_differentiableOn_of_hasFDerivAt`.
   Fourth, shrink `SourceFullFrameMaxRankChartAmbientShrink.Ωamb` by the
   preimage condition
   `sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈ D`; on this
   smaller open neighborhood prove
   `SourceFullFrameMaxRankChartAmbientShrink.chartCandidate_differentiableOn`
   by product composition, then prove
   `reconstructVector_chartCandidate_differentiableOn` from the checked
   `differentiableOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero`.
   The full-frame local section is then exactly
   `toVec G := sourceFullFrameGauge_reconstructVector d n ι M0 S
     (chartCandidate hM0 S G)`, with `toVec_mem` from the existing
   extended-tube shrink and `toVec_right_inv` from
   `reconstructInvariant_chartCandidate_eq_of_mem_relDomain`.

   The small-arity branch has an analogous but simpler target.  It must use a
   selected complex implicit chart at the actual complex extended-tube witness
   `z0`, not the real-base zero-section.  The required implementation surface
   is now Lean-pseudocode precise:

   ```lean
   noncomputable def BHW.sourceSelectedComplexGramKernelProjectionAt
       (d n : Nat)
       {z0 : Fin n -> Fin (d + 1) -> ℂ}
       (I : Fin (min n (d + 1)) -> Fin n) :
       (Fin n -> Fin (d + 1) -> ℂ) ->L[ℂ]
         LinearMap.ker
           (BHW.sourceSelectedComplexGramDifferentialToSym d n
             (min n (d + 1)) z0 I)

   noncomputable def BHW.sourceSelectedComplexGramProdMapAt
       (d n : Nat)
       {z0 : Fin n -> Fin (d + 1) -> ℂ}
       (I : Fin (min n (d + 1)) -> Fin n) :
       (Fin n -> Fin (d + 1) -> ℂ) ->
         BHW.sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
           LinearMap.ker
             (BHW.sourceSelectedComplexGramDifferentialToSym d n
               (min n (d + 1)) z0 I) :=
     fun z =>
       (BHW.sourceSelectedComplexGramMap d n (min n (d + 1)) I z,
        BHW.sourceSelectedComplexGramKernelProjectionAt d n (z0 := z0) I
          (z - z0))

   theorem BHW.contDiff_sourceSelectedComplexGramProdMapAt ...
   theorem BHW.sourceSelectedComplexGramProdMapAt_hasFDerivAt ...
   theorem BHW.sourceSelectedComplexGramProdMapAt_fderiv ...
   theorem BHW.sourceSelectedComplexGramProdMapAt_base_fderiv_isInvertible ...
   theorem BHW.sourceSelectedComplexGramProdMapAt_local_invertible_nhds ...

   noncomputable def BHW.sourceSelectedComplexGramImplicitChartAt
       (d n : Nat)
       {z0 : Fin n -> Fin (d + 1) -> ℂ}
       {I : Fin (min n (d + 1)) -> Fin n}
       {J : Fin (min n (d + 1)) -> Fin (d + 1)}
       (hI : Function.Injective I)
       (hJ : Function.Injective J)
       (hminor : BHW.sourceComplexRegularMinor d n I J z0 ≠ 0) :
       OpenPartialHomeomorph
         (Fin n -> Fin (d + 1) -> ℂ)
         (BHW.sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
           LinearMap.ker
             (BHW.sourceSelectedComplexGramDifferentialToSym d n
               (min n (d + 1)) z0 I))

   theorem BHW.sourceSelectedComplexGramImplicitChartAt_apply ...
   theorem BHW.sourceSelectedComplexGramImplicitChartAt_mem_source ...
   theorem BHW.sourceSelectedComplexGramImplicitChartAt_self ...

   noncomputable def BHW.sourceSelectedComplexZeroKernelTargetCLMAt ...
   theorem BHW.sourceSelectedComplexGramZeroSectionAt_differentiableOn ...
   theorem BHW.sourceSelectedComplexGramZeroSectionAt_selectedGram ...
   theorem BHW.sourceSelectedComplexGramZeroSectionAt_base ...
   theorem BHW.exists_sourceSelectedComplexGramZeroSectionAt_good_ball ...
   ```

   Here `sourceSelectedComplexGramImplicitChartAt` is built directly from
   `sourceSelectedComplexGramMap_hasStrictFDerivAt` and
   `sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero`.
   The good-ball theorem shrinks a flat selected-coordinate ball `D` around
   the base coordinate
   `(sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
     (sourceSelectedComplexGramMap d n (min n (d + 1)) I z0)`
   so that `q ↦ e.symm (q, 0)` lies in `ExtendedTube d n`, stays in the
   same nonzero complex-minor patch, and has invertible product-chart
   derivative.  Differentiability of the zero-section is obtained from the
   checked `SCV.openPartialHomeomorph_symm_differentiableOn_of_hasFDerivAt`
   pattern, with the forward chart smoothness supplied by
   `contDiff_sourceSelectedComplexGramProdMapAt`.

   The oriented small-arity wrapper then uses ordinary Gram coordinates only:

   ```lean
   theorem BHW.sourceOrientedMaxRank_localSection_smallArity
       {d n : Nat} [NeZero d]
       (hn : n < d + 1)
       {z0 : Fin n -> Fin (d + 1) -> ℂ}
       (hz0 : z0 ∈ BHW.ExtendedTube d n)
       (hmax :
         BHW.SourceOrientedMaxRankAt d n
           (BHW.sourceOrientedMinkowskiInvariant d n z0)) :
       BHW.SourceOrientedLocalHolomorphicSectionData (d := d) n
         (BHW.sourceOrientedMinkowskiInvariant d n z0)
   ```

   It converts `hmax` to ordinary source-Gram regularity, chooses `I,J` and
   `hminor`, defines
   `Ω := {G | sourceSelectedComplexGramFlatCoordCLM n (min n (d + 1)) I
             G.gram ∈ D}`,
   and sets
   `toVec G := e.symm (sourceSelectedComplexZeroKernelTargetCLMAt ... qG)`,
   where `qG` is the flat selected coordinate of `G.gram`.  `toVec_mem` is
   exactly the `ExtendedTube` field of the good-ball shrink.  Holomorphy is
   the composition of the continuous-linear projection `G ↦ qG` with
   `sourceSelectedComplexGramZeroSectionAt_differentiableOn`.  For
   `toVec_right_inv`, the selected-coordinate equality from
   `sourceSelectedComplexGramZeroSectionAt_selectedGram` and the checked
   variety lemma
   `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety`
   prove equality of ordinary Gram matrices; the determinant field is
   eliminated because an embedding `Fin (d + 1) ↪ Fin n` would contradict
   `hn`.

   Full-frame holomorphic-section regularity support checked, 2026-05-07:
   `SourceOrientedFullFrameHolomorphicSection.lean` now proves
   `sourceFullFrameSymmetrizeCoordCLM`,
   `differentiable_sourceFullFrameSymmetrizeCoord`,
   `differentiable_sourceFullFrameOrientedCoordOfSource`,
   `differentiable_sourceFullFrameSelectedSymmetricCoordAmbient`,
   `sourceFullFrameSelectedKernelCoordAmbient_eq_kernelProjection`,
   `sourceFullFrameGaugeSliceImplicitKernelMap_eq_kernelProjection`,
   `sourceFullFrameGaugeSliceMapSymmetric_eq_symmetrize`,
   `contDiff_sourceFullFrameGaugeSliceMapSymmetric`,
   `contDiff_sourceFullFrameGaugeSliceImplicitKernelMap`,
   `sourceFullFrameGaugeSliceImplicitKernelMap_base_fderiv_isInvertible`,
   `sourceFullFrameGaugeSliceImplicitKernelMap_local_invertible_nhds`,
   `SourceFullFrameImplicitKernelTargetRegularityData`,
   `sourceFullFrameImplicitKernelTargetRegularityData`,
   `differentiable_sourceFullFrameSelectedKernelCoordAmbient`,
   `differentiable_sourceSelectedMixedRows`,
   `SourceFullFrameMaxRankChartAmbientShrink.chartCandidate_differentiableOn_Ωamb_of_kernelSymmOn`,
   `SourceFullFrameMaxRankChartAmbientShrink.chartCandidate_differentiableOn_Ωamb`,
   `SourceFullFrameMaxRankChartAmbientShrink.restrict_kernelRegularity`,
   `SourceFullFrameMaxRankChartAmbientShrink.chartCandidate_differentiableOn_restrict_kernelRegularity`,
   and `sourceOrientedMaxRank_localSection_fullFrame`.
   Thus the inverse-regular target set `D` is no longer a blocker: it is the
   checked target `e.target ∩ e.symm ⁻¹' U`, where `U` is the source-side open
   set on which the Frechet derivative of
   `sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S` remains a
   continuous-linear equivalence.  The full-frame
   `SourceOrientedLocalHolomorphicSectionData` assembly is now also checked:
   it applies the regularity-restricted chart candidate, composes with the
   existing
   `differentiableOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero`,
   and reuses the checked tube shrink/right-inverse fields.  The remaining
   max-rank local-section implementation task was the small-arity
   arbitrary-complex-base zero-section branch.

   Max-rank holomorphic-section producer checked, 2026-05-07:
   `SourceComplexZeroSectionAt.lean` now checks the arbitrary-complex-base
   selected product chart, implicit chart, zero-kernel target, differentiable
   zero-section, selected-Gram/base equations, and the extended-tube
   good-ball shrink.  `SourceOrientedSmallArityHolomorphicSection.lean` checks
   `sourceOrientedMaxRank_localSection_smallArity`: it converts oriented
   max-rank at the actual tube witness to ordinary complex source regularity,
   chooses the nonzero selected minor by `Classical.choose`, takes
   `Ω` to be the selected flat-coordinate preimage of the good ball, and
   proves the oriented right inverse by ordinary Gram equality plus vacuity of
   the determinant-coordinate index when `n < d + 1`.
   `SourceOrientedMaxRankHolomorphicSection.lean` then checks
   `sourceOrientedExtendedTube_holomorphicLocalSection`,
   `sourceOrientedQuotientValue_holomorphicOn_maxRank`, and
   `sourceOrientedQuotientValue_continuous_locallyBounded` by plugging the
   checked small-arity/full-frame branch producer into the already checked
   scalar quotient consumers.  The local-section/descent bridge is no longer
   the theorem-2 blocker; the remaining oriented descent blocker is the
   normal analytic-space Riemann/exceptional-rank extension package described
   below.
   The oriented normal-variety support is now tied to explicit algebraic
   equations: symmetry/rank of the Gram field, determinant alternation under
   source-frame reindexing, and the Cauchy-Binet relation
   `det(G[ι,κ]) = minkowskiMetricDet d * det_ι * det_κ`.  The required
   theorem surfaces are `sourceMatrixMinor_sourceMinkowskiGram_fullFrame`,
   `sourceOrientedAlgebraicRelations`,
   `sourceOrientedAlgebraicVariety`,
   `sourceOrientedMinkowskiInvariant_mem_algebraicRelations`,
   `sourceOrientedGramVariety_subset_algebraicVariety`,
   `isClosed_sourceOrientedAlgebraicVariety`,
   `sourceOrientedGramVariety_eq_algebraic`, and
   `sourceOrientedAlgebraicVariety_normal`.  These normality surfaces carry
   `[NeZero d]` and `hd : 2 <= d`, matching the reductivity input for
   `SO_{d+1}(ℂ)`; they are not dimension-free wrappers.  The normality route
   is now decomposed through invariant rings:
   `sourceTupleCoordinateRing`,
   `specialComplexLorentzAlgebraicGroup`,
   `sourceOrientedInvariantSubalgebra`,
   `sourceOrientedInvariantRing_generated_by_gram_det`,
   `sourceOrientedInvariantRing_relations_kernel`,
   `sourceOrientedInvariantRing_integrallyClosed`,
   `sourceOrientedAlgebraicCoordinateRing_iso_invariants`, and
   `sourceOrientedAlgebraicVariety_normal_of_invariants`, followed by
   `sourceOrientedGramVariety_normal_of_algebraic`.  These are the first and
   second fundamental theorem for the special complex orthogonal group plus
   the standard fact that linearly reductive invariants of an integrally
   closed polynomial domain are integrally closed.  Normality may only come
   from this algebraic SO-invariant model or an exact standard
   invariant-theory import, not from the pure-Gram normality theorem.
   The forward actual-tuple Cauchy-Binet equation is checked in
   `SourceOrientedCauchyBinet.lean`: set
   `Mι := sourceFullFrameMatrix d n ι z` and
   `Mκ := sourceFullFrameMatrix d n κ z`, rewrite the selected source Gram
   minor as `det (Mι * ηℂ * Mκᵀ)`, then apply `Matrix.det_mul`,
   `Matrix.det_transpose`, and `minkowskiMetricDet`.  This proves the
   source-variety-to-algebraic relation direction for the determinant
   equation.  The selected-frame alternation relation is also a small
   actual-tuple theorem: `sourceFullFrameDet_reindex_selectedFrame` is
   `Matrix.det_permute` for the row-permuted selected full-frame matrix.
   `SourceOrientedAlgebraicRelations.lean` now checks the explicit algebraic
   relation set itself: `sourceOrientedAlgebraicRelations` is
   `G.gram ∈ sourceSymmetricRankLEVariety n (d + 1)` plus ordered-frame
   alternation and the Cauchy-Binet equations;
   `sourceOrientedMinkowskiInvariant_mem_algebraicRelations` combines the
   checked pure-Gram rank inclusion, determinant alternation, and
   Cauchy-Binet; `sourceOrientedGramVariety_subset_algebraicVariety` is range
   elimination; and `isClosed_sourceOrientedAlgebraicVariety` is the finite
   closed-intersection proof.  These are not the invariant-ring kernel theorem
   and do not prove `sourceOrientedGramVariety_eq_algebraic`.
   The invariant-theory import boundary is now fixed at generator/kernel
   level, not at the slogan "FFT/SFT for `SO`": the standard coordinate ideal
   is generated by pairing symmetry, `(D + 1)` pairing minors, ordered-volume
   alternation, and the Cauchy-Binet relations
   `det(q[ι,κ]) = p_ι * p_κ`; the source-side transport inserts the fixed
   factor `minkowskiMetricDet d`.  `sourceOrientedAlgebraicCoordinateRing_iso_invariants`
   must be obtained by surjectivity plus
   `Ideal.quotientKerAlgEquivOfSurjective`, after transporting the standard
   kernel theorem through
   `sourceMinkowskiToDotInvariantCoordinateEquiv`.  If this is sourced from
   ordinary invariant theory rather than proved locally, the imported theorem
   must have exactly this generator/kernel content, be sorry-free, and must
   not be introduced as an axiom or as a theorem mentioning OS, Wightman
   functions, EOW, locality, or theorem 2.
   The concrete polynomial coordinate rings and relation ideals are now
   checked in `SourceOrientedInvariantCoordinateRing.lean`: standard tuple
   coordinates, standard pairing and ordered-volume polynomials,
   `standardSOInvariantCoordinateRing`,
   `standardSOAlgebraicRelationGenerators`,
   `standardSOAlgebraicRelationIdeal`,
   `sourceOrientedInvariantCoordinateRing`,
   `sourceOrientedAlgebraicRelationGenerators`, and
   `sourceOrientedAlgebraicRelationIdeal`.  Scalar coefficients in polynomial
   relations are explicit constants via `MvPolynomial.C`; this file is only
   coordinate bookkeeping and does not assert the `SO` FFT/SFT theorem.
   `SourceOrientedInvariantCoordinateEval.lean` now checks the one-way
   zero-locus bridge needed by the relation-ideal side of the transcript:
   `sourceOrientedCoordinateEval` evaluates source-oriented invariant
   coordinate polynomials at a `SourceOrientedGramData` point, and
   `sourceOrientedAlgebraicRelationGenerators_eval_eq_zero_of_relations` plus
   `sourceOrientedAlgebraicRelationIdeal_eval_eq_zero_of_relations` prove
   that every explicit generator, and hence every polynomial in the generated
   ideal, vanishes at any point satisfying
   `sourceOrientedAlgebraicRelations`.  This remains only the forward
   pointwise relation check.  It does not prove the SFT kernel theorem, the
   radical vanishing-ideal theorem, or the reverse statement
   `sourceOrientedGramVariety_eq_algebraic`.
   The standard-dot side has the matching checked forward zero-locus support
   in `SourceOrientedInvariantCoordinateStandardEval.lean`.  It defines
   `standardSOCoordinateEval`, proves the standard Cauchy-Binet identity
   `sourceMatrixMinor_sourceComplexDotGram_standardFullFrame`, and checks
   `standardSOAlgebraicRelationGenerators_eval_eq_zero` and
   `standardSOAlgebraicRelationIdeal_eval_eq_zero` for actual dot-tuples.
   This narrows the future SFT target by confirming the displayed standard
   relations really vanish on tuple invariants, but it still does not prove
   that these relations generate the invariant-coordinate map kernel.
   The concrete tuple-level source/dot determinant scale is also checked in
   `SourceOrientedMinkowskiDotTransport.lean`.  The forward map sends a source
   selected determinant to `sourceMinkowskiToDotDetScale d` times the standard
   selected volume, while the contravariant source-to-dot coordinate-ring map
   must use `sourceMinkowskiToDotInvDetScale d` times the standard volume,
   because it evaluates source polynomials after pulling a dot tuple back by
   `(complexMinkowskiToDotLinearEquiv d).symm`.  The checked theorems are
   `sourceMinkowskiGram_after_complexMinkowskiToDotLinearEquiv_symm`,
   `standardFullFrameDet_after_complexMinkowskiToDotLinearEquiv`, and
   `sourceFullFrameDet_after_complexMinkowskiToDotLinearEquiv_symm`, with both
   determinant scales proved nonzero.  This corrects the future coordinate
   transport contract: determinant variables are transported by the inverse
   scale in the coordinate-ring direction.
   The next production slice is now Lean-mechanical: add the source tuple
   polynomial ring
   `sourceTupleCoordinateRing d n = MvPolynomial (Fin n × Fin (d + 1)) ℂ`,
   the source Gram polynomial
   `∑ μ, C (MinkowskiSpace.metricSignature d μ) * X (i, μ) * X (j, μ)`,
   and the source selected determinant polynomial
   `Matrix.det (fun a μ => X (ι a, μ))`.  The contravariant transport is the
   algebra equivalence induced by the diagonal inverse Wick scale on variables:
   source variables map to
   `C (complexMinkowskiDotInvScale d μ) * X (i, μ)` and standard-dot
   variables map back to `C (complexMinkowskiDotScale d μ) * X (i, μ)`.
   Variable inverse proofs are `MvPolynomial.algHom_ext` plus the pointwise
   scale identities
   `complexMinkowskiDotInvScale_mul_scale` and
   `complexMinkowskiDotScale_mul_invScale`.  The generator images are then:
   Gram polynomials map exactly to `standardPairingCoordinatePolynomial`
   because
   `(MinkowskiSpace.metricSignature d μ : ℂ) *
      complexMinkowskiDotInvScale d μ *
      complexMinkowskiDotInvScale d μ = 1`;
   determinant polynomials map to
   `MvPolynomial.C (sourceMinkowskiToDotInvDetScale d) *
      standardVolumeCoordinatePolynomial (d + 1) n ι`
   by `AlgHom.map_det`, rewriting the matrix as multiplication by the
   diagonal inverse-scale matrix, and `Matrix.det_mul`.  This coordinate
   equivalence carries no dimension hypothesis; `[NeZero d]` and `hd : 2 <= d`
   enter only later for reductivity/normality.  This is now checked in
   `SourceOrientedInvariantCoordinateTransport.lean`, including
   `sourceMinkowskiToDotCoordinateRingEquiv`,
   `sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceGram`,
   `sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceDet`, the
   pairing/volume adjoin transport theorem, and the matching invariant
   coordinate equivalence
   `sourceMinkowskiToDotInvariantCoordinateEquiv`.
   The relation-ideal transport is now checked and generator-level mechanical.
   Under
   `sourceMinkowskiToDotInvariantCoordinateEquiv`, source symmetry and rank
   minor generators map exactly to the corresponding standard-dot generators.
   Source determinant-alternation generators map to
   `MvPolynomial.C (sourceMinkowskiToDotInvDetScale d)` times the standard
   alternation generators, so ideal membership is preserved by scalar
   multiplication; the reverse direction multiplies the mapped source
   alternation generator by `MvPolynomial.C (sourceMinkowskiToDotDetScale d)`
   and uses `sourceMinkowskiToDotDetScale_mul_invDetScale`.  Source
   Cauchy-Binet generators map exactly to standard Cauchy-Binet generators
   because
   `minkowskiMetricDet d * sourceMinkowskiToDotInvDetScale d *
      sourceMinkowskiToDotInvDetScale d = 1`.  Therefore
   `sourceOrientedRelationIdeal_transport_dot` is only `Ideal.map_span`,
   `Ideal.span_le`, and the four generator-image calculations; it does not
   invoke the standard `SO` SFT theorem.
   The generator-coordinate map layer is now checked in
   `SourceOrientedInvariantCoordinateMap.lean` and must be kept separate from
   the genuine `SO` FFT/SFT theorem.  It defines
   `standardSOGeneratorSubalgebra D n` to be the algebra generated in
   `standardTupleCoordinateRing D n` by the checked pairing and ordered-volume
   polynomials, and `sourceOrientedGeneratorSubalgebra d n` analogously
   from the source Gram and selected determinant polynomials.  The maps
   `standardSOGeneratorCoordinateMap` and
   `sourceOrientedGeneratorCoordinateMap` are just `MvPolynomial.aeval` into
   those generated subalgebras: `Sum.inl ij` goes to the corresponding
   pairing/Gram generator element and `Sum.inr ι` goes to the corresponding
   volume/determinant generator element.  Surjectivity is proved by
   `Algebra.adjoin_induction` on the subtype membership in the generated
   subalgebra; constants use `MvPolynomial.C`, generator cases use the
   matching variable, and add/mul cases use closure of the algebra-map range.
   The source/dot generator-subalgebra transport is then a `simpa` wrapper
   around the already checked
   `sourceMinkowskiToDotCoordinateRingEquiv_adjoin_pairing_volume`.
   Restricting the tuple-coordinate equivalence gives
   `sourceMinkowskiToDotGeneratorSubalgebraEquiv`, and polynomial induction
   proves the commutative square
   `sourceMinkowskiToDotGeneratorCoordinateMap_commutes`.  The determinant
   generator case is exactly the inverse determinant-scale calculation already
   checked for
   `sourceMinkowskiToDotCoordinateRingEquiv_apply_sourceDet`.  None of these
   declarations says that the generated subalgebra is the full invariant
   subalgebra; that equality remains the actual FFT input.
   The actual standard-dot invariant subalgebra layer is the next checked
   finite-dimensional support slice.  Use `SOComplex D` and define the
   contravariant polynomial action
   `standardSOCoordinateAction D n g` by
   `X (i, μ) ↦ ∑ ν, C (g.val μ ν) * X (i, ν)`.  Pairing invariance is the
   dot-product calculation
   `(g *ᵥ Xi) ⬝ᵥ (g *ᵥ Xj) = Xi ⬝ᵥ Xj`, using
   `Matrix.dotProduct_mulVec`, `Matrix.vecMul_mulVec`, and
   `g.orthogonal : g.val.transpose * g.val = 1`, mapped into the polynomial
   ring.  Volume invariance rewrites the transformed selected-frame matrix as
   `M * (g.val.map C).transpose`, then uses `Matrix.det_mul`,
   `Matrix.det_transpose`, and `g.proper : g.val.det = 1`.  Define
   `standardSOInvariantSubalgebra D n` as the fixed subalgebra of this action,
   prove both generator families lie in it, and obtain
   `standardSOGeneratorSubalgebra_le_invariantSubalgebra` by
   `Algebra.adjoin_le`.
   The actual invariant-coordinate map is then the generated-coordinate map
   followed by this inclusion.  Its surjectivity is not unconditional:
   `standardSOInvariantCoordinateMap_surjective_of_generator_eq` takes exactly
   the FFT equality
   `standardSOInvariantSubalgebra D n = standardSOGeneratorSubalgebra D n` and
   combines it with the already checked generated-coordinate map surjectivity.
   Thus the production Lean boundary for the FFT is now reduced to the reverse
   inclusion of the actual fixed subalgebra into the generated one.
   The theorem-2 blueprint now tightens this into the single standard-dot
   support surface `BHW.standardSO_FFT_SFT_coordinatePresentation`, whose three
   outputs are: FFT generation by pairings and ordered volumes, SFT kernel
   equality with the explicit symmetry/minor/alternation/Cauchy-Binet ideal,
   and surjectivity of `BHW.standardSOInvariantCoordinateMap`.  Lean may not
   cite a slogan-level "FFT/SFT for SO" theorem with incompatible coordinates,
   and may not proceed to the oriented normality theorem unless those three
   outputs are available from the same sorry-free proof or source theorem.
   The surjectivity output is no longer a named black box inside that package:
   the blueprint now splits it through the invariant subtype elements
   `BHW.standardPairingInvariantElement` and
   `BHW.standardVolumeInvariantElement`, the variable-image lemmas
   `BHW.standardSOInvariantCoordinateMap_apply_pairing` and
   `BHW.standardSOInvariantCoordinateMap_apply_volume`, the polynomial-range
   lemma `BHW.algHom_range_le_adjoin_images_mvPolynomial_X`, the exact range
   theorem
   `BHW.standardSOInvariantCoordinateMap_range_eq_generator_adjoin`, and the
   subtype-adjoin lift
   `BHW.standardSOInvariantSubalgebra_mem_generator_adjoin_of_underlying`.
   Then `BHW.standardSOInvariantCoordinateMap_surjective_of_generators` is
   only `AlgHom.range_eq_top` after rewriting the FFT generator equality.
   This prevents Lean from smuggling coordinate-ring surjectivity into the
   SFT kernel theorem.
   The generic algebra plumbing for this split is now checked in
   `SourceOrientedInvariantAlgebraSupport.lean`:
   `algHom_range_le_adjoin_images_mvPolynomial_X`,
   `algEquivMapSubalgebra`, `algEquivMapIdeal`,
   `algEquivOfMappedSubalgebraEq`, `algEquivMapSubalgebra_injective`,
   `algEquivMapIdeal_injective`, and `surjective_of_algEquiv_transport`.
   The remaining unchecked part is therefore the actual standard `SO`
   generator/kernel theorem and its concrete source/dot coordinate transport,
   not the formal range/surjectivity/equivalence bookkeeping.
   The downstream coordinate-ring isomorphism is also now explicit:
   `BHW.sourceOrientedInvariantCoordinateMap_surjective` is transported from
   the standard-dot map through
   `BHW.sourceMinkowskiToDotInvariantSubalgebraEquiv` and
   `BHW.sourceMinkowskiToDotInvariantCoordinateMap_commutes`; then
   `BHW.sourceOrientedAlgebraicCoordinateRing_iso_invariants` is exactly
   `BHW.sourceOrientedCoordinateRing_quotient_relationIdeal` followed by
   `Ideal.quotientEquivOfEq` and
   `Ideal.quotientKerAlgEquivOfSurjective`.  The vanishing-ideal input is
   isolated as
   `BHW.sourceOrientedAlgebraicRelationIdeal_radical_vanishing`, so the
   normality proof cannot hide a second algebraic-geometry theorem inside the
   coordinate-ring equivalence.  That vanishing-ideal theorem now carries the
   same `hd : 2 <= d` hypothesis as the SFT kernel theorem and is proved by
   radicality of the kernel of `sourceOrientedInvariantCoordinateMap`,
   reducedness of the invariant subalgebra, and the zero-locus equation for
   `sourceOrientedAlgebraicVariety`; it is not a dimension-free definitional
   rewrite.
   The linearly reductive/integral-closure input is likewise isolated as the
   standard finite-dimensional theorem
   `BHW.specialComplexOrthogonalGroup_linearlyReductive` plus
   `BHW.linearlyReductive_invariants_integrallyClosed`; it is ordinary
   algebraic geometry and cannot mention any OS/BHW analytic object.
   The removable step now also has explicit oriented inputs:
   `sourceOrientedExceptionalRank_eq_lowerRank`,
   `sourceOrientedExceptionalRank_isAnalyticSubvariety`, and
   `sourceOrientedMaxRank_dense_in_domain`.  The rank-identification theorem
   `sourceOrientedExceptionalRank_eq_lowerRank` is a purely checked rank
   bridge: an oriented-variety point is an actual oriented source invariant,
   so `sourceGramMatrixRank_le_spacetime_source_min` bounds its Gram rank by
   `min (d + 1) n`, and failure of the defining max-rank equality is exactly
   the strict lower-rank inequality.  The determinant-zero-locus bridge
   `sourceOrientedExceptionalRank_eq_minorsVanishing` is also checked: strict
   lower rank is equivalent to vanishing of all maximal source-Gram minors,
   with the `min (d + 1) n = 0` edge case handled by
   `sourceMatrixMinor_zero_ne_zero`.  Its closedness as a finite determinant
   zero locus is checked as
   `isClosed_sourceOrientedMaximalMinorsVanishing`, using
   `continuous_sourceMatrixMinor` and `continuous_sourceOrientedGramData_gram`.
   The analytic-subvariety upgrade
   `sourceOrientedExceptionalRank_isAnalyticSubvariety` is checked in
   `SourceOrientedAnalyticSubvariety.lean`: it introduces the generic
   finite-equation predicate `IsAnalyticSubvarietyIn`, uses `U0 = univ`,
   enumerates the finite index type of maximal minor pairs by
   `Fintype.equivFin`, sets each equation to
   `G ↦ sourceMatrixMinor n (min (d + 1) n) I J G.gram`, discharges
   differentiability by the polynomial differentiability of `Matrix.det` and
   the product-coordinate Gram projection, and closes the set equality with
   `sourceOrientedExceptionalRank_eq_minorsVanishing`.  This is finite
   analytic-subvariety packaging for a checked determinant locus, not rank
   algebra, topology of zero sets, or normality.  The domain-density proof is now
   checked in `SourceOrientedDomainDensity.lean` in two layers.  First
   `sourceOrientedMaxRank_dense_in_domain_inter_maxRank` proves closure of the
   explicit max-rank locus: max-rank centers are immediate by
   `subset_closure`, while rank-deficient centers use
   `sourceOriented_rankDeficient_residualChart`, the chart center equation
   `toVec_c0_invariant`, and `maxRank_dense_parameters`; the dense parameter
   image is pushed into
   `sourceOrientedExtendedTubeDomain ∩ {G | SourceOrientedMaxRankAt d n G}` by
   `P_subset_K` and the chart's `toVec_mem`.  Then
   `sourceOrientedMaxRank_dense_in_domain` rewrites that checked dense locus as
   the non-exceptional complement using `not_exceptional_rank_iff_maxRank` on
   the oriented extended-tube image.
   The normal-space Riemann
   theorem is the same finite-dimensional-polymorphic
   `normalAnalyticSubvariety_riemannExtension`/`weaklyHolomorphic` theorem
   used by the ordinary scalar route, not a scalar-coordinate-only theorem.
   The oriented call first converts
   `IsRelOpenInSourceOrientedGramVariety` to the generic
   `IsRelOpenIn`, then reorders the returned `(domain-control, EqOn)` pair
   into the `SourceOrientedVarietyGermHolomorphicOn` field order.  It consumes
   relative openness of `sourceOrientedExtendedTubeDomain`,
   continuity/local boundedness of the quotient value, and max-rank local
   charts; it may not silently assert removability from normality alone.
   The oriented real-uniqueness anchor now has an explicit tangent/regularity
   subpacket: `sourceFullFrameDetDifferential`,
   `sourceFullFrameDetDifferentialLinear`,
   `sourceFullFrameDetContinuousLinearMap`,
   `sourceOrientedDifferential`,
   `sourceOrientedDifferentialLinear`,
   `sourceOrientedDifferentialCLM`,
   `sourceOrientedMinkowskiInvariant_hasFDerivAt`,
   `sourceOrientedDifferential_real_complexification`,
   `sourceOrientedRegularAt_of_pureGram_regular_plus_detRank`, and
   `sourceOrientedComplexifiedRealTangentEqualsComplexTangent_of_detJacobian`.
   These are the finite-dimensional reasons the π-permuted real patch remains
   a maximal totally real uniqueness set after determinant coordinates are
   added; they cannot be inferred by reusing the pure-Gram tangent theorem.
   The real-patch producer is now also explicit:
   `SourceOrientedJacobianExpectedRankAt`,
   `sourceOrientedRegularAt_iff_expectedRealJacobianRank`,
   `sourceOrientedTotallyReal_of_expectedRealJacobianRank`,
   `sourceOrientedRealEnvironment_smallArity_of_pureGram`,
   `sourceOrientedRealEnvironment_fullFrameSubpatch`, and
   `os45Figure24_realPatch_orientedRegularSubpatch`.  The adjacent compact
   seed must shrink to a nonempty open oriented-regular subpatch; it may not
   reuse the pure-Gram `gramEnvironment`, because that carrier has forgotten
   determinant-coordinate signs.  The full-frame branch of that shrink is now
   explicit through
   `IsOS45Figure24CheckedRealPatch`,
   `sourceRealFullFrameDet_nonzero_isOpen`,
   `sourceRealFullFrameDet_nonzero_dense`,
   `nonempty_open_inter_sourceRealFullFrameDet_nonzero`,
   `IsHWRealEnvironment.restrict_sourceOpen`,
   `isOpen_realSourcePermuteImage`,
   `nonempty_realSourcePermuteImage`, and
   `os45Figure24_checkedRealPatch_fullFrameSubpatch`: after π-permutation,
   choose the fixed head full-frame embedding, intersect the π-permuted patch
   with the dense open nonvanishing determinant locus, pull that determinant
   subpatch back by the real source-permutation homeomorphism, preserve the
   pure-Gram real environment by the open-subpatch restriction theorem, and
   only then call
   `sourceOrientedRealEnvironment_fullFrameSubpatch`.
   The oriented adjacent `S'_n` consumers now have concrete data shapes:
   `OS45AdjacentSPrimeOrientedScalarizationChart`,
   the proposition alias `OS45AdjacentSPrimeOrientedSourceEq`,
   `OS45AdjacentSPrimeOrientedScalarSeed`, and
   `OS45AdjacentSPrimeOrientedSeedFigure24Path` store the connected oriented
   corridor `Wscal`, the seed domain `Wseed`, double-domain membership,
   provenance from the Figure-2-4 source patch, and the final corridor
   equality.  These structures prevent the active route from feeding an
   oriented representative through pure-Gram `S'_n` theorem surfaces.
   The oriented route has one additional OS45 obligation that the current
   public pure-Gram source patch does not yet expose: every Figure-2-4
   path/corridor theorem must carry
   `BHW.OS45Figure24OrientedPathField`, proving equality of the full oriented
   invariant along the selected path, not only equality of
   `sourceMinkowskiGram`.  The local API audit narrows this obligation:
   `BHW.figure24RotateAdjacentConfig_lorentz_inverse` already supplies a
   `Λinv : ComplexLorentzGroup d` with
   `complexLorentzAction Λinv (Δ t) = permAct τ (Γ t)`, and the underlying
   `(3,4,5)` rotation has `proper := spatialRotMatrix12_det`.  Thus
   determinant-`1` control of the specific Figure-2-4 rotation is checked.
   The finite determinant algebra and base oriented source-variety scaffolding
   are now checked in `SourceOriented.lean`, including
   `BHW.sourceFullFrameDet_permAct`,
   `BHW.sourceOrientedMinkowskiInvariant_complexLorentzAction`,
   `BHW.sourceOrientedMinkowskiInvariant_permAct`,
   `BHW.sourcePermuteOrientedGram_mem_variety_iff`, and the conditional
   double-domain relative-open theorem
   `BHW.sourceOrientedDoublePermutationDomain_relOpen_of_sourceOrientedExtendedTubeDomain`,
   together with the oriented germ operations
   `BHW.SourceOrientedVarietyGermHolomorphicOn.sub` and
   `BHW.SourceOrientedVarietyGermHolomorphicOn.precomp_sourcePermuteOrientedGram`.
   The strengthened Figure-2-4 environment/source-patch slice exposing the
   same rotated `Δ` as the checked pure-Gram patch is now a named lower
   producer group; after it, the active oriented route still has the
   branch-law/descent and adjacent producer layers.  The oriented path still
   cannot be recovered later by choosing arbitrary lifts of the Gram path.
   This strengthened group is split into explicit producer names:
   `BHW.OS45Figure24RotatedPathFormulaField`,
   `BHW.swFigure24_adjacentPathStableNeighborhood_rotated_exists`,
   `BHW.swFigure24_adjacentHorizontalEnvironmentWithRotatedPathStability`,
   `BHW.OS45Figure24OrientedPathField_of_checked_figure24`,
   `BHW.os45_adjacent_identity_horizontalEdge_sourcePatch_with_orientedPath`,
   and the later canonical-patch extension
   `BHW.OS45Figure24OrientedCanonicalSourcePatchData` produced by
   `BHW.os45_adjacent_identity_canonicalSourcePatch_with_orientedPath`.  The
   existing checked `hV_figPath_closure` field is pure-Gram only and is too
   lossy for determinant signs; the oriented theorem must preserve the
   definitional rotated path formula before projecting to Gram coordinates.
   The determinant algebra now has implementation-grade pseudo-code in the
   blueprint: the selected frame matrix is
   `fun a μ => z (ι a) μ`, `complexLorentzAction Λ` sends it to
   `Z * Λ.val.transpose`, `Matrix.det_mul`, `Matrix.det_transpose`, and
   `Λ.proper` prove determinant invariance, and permutation transports
   `ι` to `ι.trans σ.toEmbedding` without inserting a hidden row sign.
   The blueprint now also records the oriented downstream migration ledger:
   `BHW.sourceOrientedGramVariety`,
   `BHW.sourceOrientedDoublePermutationDomain`,
   `BHW.sourcePermuteOrientedGram_mem_variety_iff`,
   `BHW.sourceOrientedDoublePermutationDomain_relOpen_of_sourceOrientedExtendedTubeDomain`,
   `BHW.SourceOrientedVarietyGermHolomorphicOn.precomp_sourcePermuteOrientedGram` (checked),
   and `BHW.sourceOrientedGramVariety_identity_principle`, followed by the
   oriented adjacent `S'_n` surfaces
   `BHW.os45AdjacentSPrimeOrientedScalarizationChart_of_figure24`,
   `BHW.os45AdjacentSPrimeOrientedSourceEq_of_compactWickPairingEq`,
   `BHW.os45AdjacentSPrimeOrientedScalarSeed_of_compactWickPairingEq`, and
   `BHW.os45AdjacentSPrimeOrientedSeedFigure24Path`, with the orchestration
   wrapper
   `BHW.os45AdjacentSPrimeOrientedSeedFigure24Path_of_compactWickPairingEq`.
   The path-facing seed theorem now has an implementation-level assembly
   proof: it stores the supplied `hOrientedPath`, calls
   `BHW.os45AdjacentOrientedScalarEq_on_quarterTurnCorridor` to produce
   `corridor_eq`, and uses the stored `hSeed.τ_eq` both to rewrite the
   double-domain hypothesis from `hSeed.τ` to the fixed adjacent swap and to
   rewrite the final corridor equality back into the structure's `hSeed.τ`
   form.  This prevents a later Lean proof from accidentally propagating along
   a different adjacent permutation.
   These are not aliases for the pure-Gram names; they are required if the
   strict proper-complex route uses
   `SourceOrientedScalarRepresentativeData`.
   One further correction is now explicit: the old
   `SourceDistributionalAdjacentTubeAnchor.gramEnvironment` cannot be reused
   on the oriented route, because it stores only real Gram matrices and has
   forgotten the full-frame determinant signs.  The oriented route needs
   `BHW.sourceRealOrientedMinkowskiInvariant`,
   `BHW.sourceOrientedDistributionalUniquenessPatch`,
   `BHW.SourceOrientedDistributionalAdjacentTubeAnchor`, and the generic
   propagation theorem
   `BHW.os45AdjacentOrientedScalarEq_on_quarterTurnCorridor`.  The hard
   identity-principle input for that propagation is now decomposed in the
   blueprint: `sourceOrientedGramVariety_identity_principle_smallArity`
   transports the checked pure-Gram identity theorem across the empty
   determinant-coordinate equivalence when `n < d + 1`;
   the checked seed-specific theorem
   `sourceOrientedGramVariety_maxRank_identity_principle_of_connected_fullFrame`
   propagates zero from a nonempty relatively open seed already contained in
   the smooth oriented max-rank stratum; and
   `sourceOrientedGramVariety_relOpen_eqOn_zero_of_eqOn_maxRank` extends the
   result to all of a relatively open connected domain by continuity and
   density of max rank.  The max-rank identity theorem is no longer just a
   slogan: it now mirrors the checked pure-Gram clopen proof, with
   `sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame`,
   `SourceOrientedVarietyGermHolomorphicOn.to_maxRank_chart`, and
   `SourceOrientedMaxRankChartData.local_identity_near_point` supplying the local
   analytic continuation step on arbitrary complex max-rank points.  The local
   step is itself decomposed: `SourceOrientedMaxRankChartData.shrink_to_relOpen`
   shrinks the chart to a connected open image inside the given relative
   domain; `LocalBiholomorphOnSourceOrientedVariety.image_relOpenIn_chart`
   turns relative openness in the source variety into relative openness in the
   chart image; and `SCV.identity_theorem_connected_open_zero` is the standard
   connected-domain holomorphic identity theorem for a nonempty open zero
   subset.  The
   checked equality form
   `sourceOrientedGramVariety_maxRank_eqOn_of_connected_fullFrame` is the
   branch-propagation surface consumed by the BHW/Jost closed-loop seed.  The
   hard-range relative-openness helper
   `sourceOrientedRelOpen_inter_maxRank_relOpen` is also checked: on the
   oriented source variety, max rank is the union of the selected
   full-frame determinant-nonzero sheets.
   The density/continuity extension is now checked too:
   `sourceOrientedMaxRank_dense_in_relOpen_inter` pulls an ambient
   neighborhood back to source tuples, perturbs to a complex-regular source
   tuple by `dense_sourceComplexGramRegularAt`, and pushes forward to a
   max-rank oriented invariant; `sourceOrientedRelOpen_inter_maxRank_nonempty`
   and `sourceOrientedGramVariety_relOpen_eqOn_zero_of_eqOn_maxRank` are the
   nonemptiness and continuity consequences.  Thus
   `sourceOrientedGramVariety_identity_principle_of_connected_maxRank_fullFrame`
   and `sourceOrientedGramVariety_eqOn_of_connected_maxRank_fullFrame` now
   propagate zero/equality on all of a relatively open oriented patch once
   the max-rank part of that patch is connected.
   The
   closed-loop consumers
   `bhw_jost_closedChain_orientedMaxRankMonodromy_of_seed` and
   `bhw_jost_closedChain_sourceMonodromy_on_maxRankClosingPatch_of_seed` are
   now checked: given a stored `BHWJostOrientedMaxRankClosedLoopSeed` and
   connectedness of the max-rank part of the closing oriented patch, they
   propagate terminal-initial germ equality, and then terminal-`B0` source
   branch equality, on the max-rank closing patch.  The stronger consumers
   `bhw_jost_closedChain_orientedMonodromy_of_seed` and
   `bhw_jost_closedChain_sourceMonodromy_of_seed` then use the checked
   density/continuity extension to reach the whole closing patch.  They
   deliberately do not assert the genuine Hall-Wightman seed and still take
   connectedness of the closing max-rank part as an explicit geometric input.
   The
   final continuity extension is pinned to the generic topology helper
   `continuousOn_eqOn_zero_of_subset_closure` and to
   `sourceOrientedMaxRank_dense_in_relOpen_inter`, not to a prose density
   argument.  The remaining non-mechanical producers for the all-rank identity
   theorem are
   `sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected`, the complex
   max-rank density theorem, and the continuity/density extension beyond the
   max-rank stratum; the max-rank seed-propagation theorem itself is no longer
   an unnamed analytic gap.  The
   max-rank connectedness producer is also now split: prove the exceptional
   lower-rank locus is an analytic
   subvariety of oriented complex codimension at least one, use the local
   connected basis to get a locally path-connected analytic-space structure on
   `sourceOrientedGramVariety d n`, and apply the ordinary SCV/topology theorem
   `connected_relOpen_complement_of_analytic_codim_ge_one` to
   `U \ SourceOrientedExceptionalRank`; the equality with
   `U ∩ SourceOrientedMaxRankAt` is then definitional inside the oriented
   variety.
   The hard
   source input in this mini-packet is the oriented real-patch uniqueness
   predicate for the fixed adjacent pair `(i, hi)`, on the π-permuted real
   patch `{y | ∃ x ∈ hAnchor.realPatch π, y = fun k => x (π k)}`;
   `oriented_right_eq_perm_left` is only finite algebra from
   `sourceOrientedMinkowskiInvariant_permAct`.  The oriented anchor must also
   retain the real left/right extended-tube sector fields and the
   `realPatch_commonEdge_contact` provenance field; oriented-domain image
   membership alone is not enough to apply `hRep.branch_eq` to the specific
   real points, and raw sector membership alone is not enough to prove that
   the real common-edge patch meets `hChart.Wscal`.  The contact is with the
   real common-edge source invariant via `hChart.commonEdge_mem`, not with
   the quarter-turn complex endpoint carried by `hChart.quarterTurn_mem`.
   This field must be supplied by the corrected two-point canonical source
   patch: `xseed` is the ordered perturbation, `xcontact =
   os45CommonEdgeRealPoint 1 xseed` is also in the same canonical patch, and
   the `π`-real-patch contact point is the source permutation of `xcontact`.
   No proof may use an equal-time assertion about `xseed`.
   The predicate `sourceOrientedDistributionalUniquenessPatch` is now
   decomposed further: it must be produced from
   `BHW.IsHWOrientedRealEnvironment` by
   `BHW.sourceOrientedDistributionalUniquenessPatch_of_HWRealEnvironment`,
   through the local seed theorem
   `BHW.sourceOrientedLocalTotallyRealIdentity_seed`.  That seed theorem uses
   `BHW.sourceOrientedLocalChart_at`,
   `BHW.sourceOrientedLocalChart_totallyRealSlice`,
   `BHW.sourceOrientedLocalChart_shrink_to_domain_and_realPatch`,
   `BHW.sourceOrientedRestrictedRealSlice`,
   `BHW.sourceOrientedLocalChart_totallyRealSlice_restrict`,
   `BHW.realCoord_seed_nonempty_open_in_restrictedSlice`,
   `BHW.SourceOrientedVarietyGermHolomorphicOn.to_chart`, and
   `SCV.identity_theorem_totally_real` to produce a nonempty relatively open
   oriented subset `W ⊆ U` where two oriented germ-holomorphic functions
   agree.  The shrink now returns both a connected oriented neighborhood `Ω`
   and an open real seed `Eseed`, with `C.chart '' Ω` open and connected.
   The blueprint pins `BHW.NonemptyOpenInTotallyRealSlice` as the exact input
   to `SCV.identity_theorem_totally_real` on the restricted slice inside
   `C.chart '' Ω`; the proof must not apply the identity theorem on the
   larger `C.chart '' C.Ω` while the pulled-back functions are only
   holomorphic on `C.chart '' Ω`.  The local slice data must also expose
   `realCoord_openMap_on_E0`, since openness of the real seed image in the
   restricted totally-real slice is a coordinate-chart theorem, not a formal
   consequence of `IsOpen Eseed`.  `to_chart` is now factored through
   `LocalBiholomorphOnSourceOrientedVariety`: the chart API exposes an inverse,
   left/right inverse laws, inverse membership, and inverse differentiability/
   continuity on the chart image.  The proof of
   `LocalBiholomorphOnSourceOrientedVariety.germ_to_chart` is local: at
   `y ∈ chart '' Ω`, use `ContinuousOn` of the inverse to shrink inside the
   germ representative's ambient open set, compose that representative with
   the differentiable inverse, and glue the local differentiability statements
   by `differentiableOn_of_local_agreement`.  Thus `to_chart` returns an actual
   holomorphic representative on `C.chart '' Ω` agreeing with the source germ
   on `Ω`; it cannot choose a new scalar representative or forget the shrink
   `Ω ⊆ C.Ω`.  Only then may
   `sourceOrientedDistributionalUniquenessPatch_of_HWRealEnvironment` call
   `sourceOrientedGramVariety_identity_principle` to propagate the equality
   over the connected `U`.  This is finite-dimensional invariant-theory/SCV
   support, not a QFT axiom; it cannot be inferred from the pure-Gram
   real-tangent theorem because the oriented determinant coordinates add
   extra tangent equations.  The local chart producer is now pinned to the
   finite-dimensional implicit-function theorem for
   `sourceOrientedDefiningEquations`: prove
   `sourceOrientedGramVariety_eq_zeroLocus_definingEquations`,
   `sourceOrientedDefiningEquations_hasFDerivAt`, and
   `sourceOrientedRegularAt_submersion_equations`, then apply
   `localBiholomorphOn_zeroLocus_of_submersion`.  The totally-real slice is
   produced only after the defining equations' real coefficients and the
   tangent-complexification equality are proved.
   Gemini Deep Research interaction
   `v1_ChczMGoxYWNQTEphYWlfdU1QeFlpRTJBSRIXMzBqMWFjUExKYWFpX3VNUHhZaUUyQUk`
   independently confirmed this route-risk classification: proper
   determinant-`1` complex Lorentz invariance leaves the
   determinant/pseudoscalar obstruction in full scalar rank, and
   `BHW.bvt_F_realOrthoChronousInvariant` cannot be derived from local
   `SO(d+1)` OS.E1 plus proper-complex invariance without adding parity.
   This is an audit result, not a proof or an axiom approval.
   The strengthened complex predicate itself is now pinned as forward-tube
   overlap invariance for all
   `BHW.HallWightmanFullComplexLorentzGroup d` elements:
   `F (A • z) = F z` whenever both `z` and `A • z` lie in
   `BHW.ForwardTube d n`.  The extended-tube improper equality then has a
   concrete proof transcript: choose proper forward-tube preimages
   `z = Γz • pz` and `w = Γw • qw`, form the full element
   `Γw⁻¹ * A * Γz`, use the forward-tube overlap invariant to prove
   `F qw = F pz`, and unfold the two `extendF` values by the same preimage
   equality lemma used in the determinant-`1` case.  The finite support slots
   still missing here are
   `BHW.fullComplexLorentz_properInv_mul_full_mul_proper`,
   `BHW.fullComplexLorentz_preimage_map_eq`, and
   `BHW.extendF_eq_preimage_value`.

   Readiness status for this scalar-source packet: the theorem names,
   dimension-general conventions, germ-holomorphic API, and Lean-shaped
   assembly are now pinned.  The remaining mathematical gaps are exactly the
   unimplemented proof obligations for the ordinary branch law, including the
   newly explicit improper-component/orientation gate, Lemma-3 relative
   openness, max-rank scalar chart, scalar continuity/local boundedness, and
   normal analytic-space removability.  Therefore the proof
   docs are still not at the "100% ready for production Lean" threshold for
   `BHW.sourceScalarRepresentativeData_bvt_F`.

1. `BHW.extendedTube_same_sourceGram_extendF_eq`: for `z,w ∈
   BHW.ExtendedTube d n`, equality of
   `BHW.sourceMinkowskiGram d n z` and
   `BHW.sourceMinkowskiGram d n w` implies
   `BHW.extendF F z = BHW.extendF F w`, under holomorphy of `F` on the forward
   tube and complex Lorentz invariance on forward-tube overlaps.  This is the
   ordinary Hall-Wightman branch law, not PET branch independence.  The
   scalar-rank split must be the Hall-Wightman split, not the local
   source-map-regularity predicate.  Introduce
   `BHW.sourceGramMatrixRank`, `BHW.HWSourceGramOrbitRank`, and
   `BHW.HWSourceGramLowRank`; for spacetime dimension `d + 1`, the direct
   orbit branch is scalar rank at least `min d n`, and the limiting branch is
   scalar rank `< min d n`.  In the original four-vector paper this is rank
   three or four in the hard arity range, and nonsingular scalar matrices in
   the small-arity range.  The theorem-2 blueprint now expands this into the
   Lean-facing Lemma-2 alternative:
   `BHW.hw_sameSourceGram_fiberAlternative`, the high scalar-rank orbit theorem
   with its coefficient-quotient support
   `BHW.sourceCoefficientEval`,
   `BHW.sourceCoefficientGramMap`,
   `BHW.sourceCoefficientGramKernel`,
   `BHW.sourceCoefficientGramMap_apply_sourceMinkowskiGram`,
   `BHW.sourceCoefficientEval_single`,
   `BHW.sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero`,
   `BHW.sourceCoefficientEval_pair_eq_sum_gram`,
   `BHW.sourceCoefficientEval_ker_le_gramKernel`,
   `BHW.restrictedMinkowskiLeftMap`,
   `BHW.restrictedMinkowskiRadical`,
   `BHW.restrictedMinkowskiRank`,
   `BHW.sourceCoefficientGramMap_eq_toLin_transpose`,
   `BHW.sourceGramMatrixRank_eq_finrank_range_sourceCoefficientGramMap`,
   `BHW.sourceCoefficientEval_mem_restrictedMinkowskiRadical_iff`,
   `BHW.sourceCoefficientGramKernel_eq_eval_preimage_radical`,
   `BHW.finrank_range_sourceCoefficientGramMap_eq_restrictedRank`,
   `BHW.sourceGramMatrixRank_eq_restrictedMinkowskiRank_range`,
   `BHW.restrictedMinkowskiRadical_nontrivial_of_degenerate`,
   `BHW.restrictedMinkowskiRank_lt_finrank_of_degenerate`,
   `BHW.finrank_range_sourceCoefficientEval_le`,
   `BHW.finrank_restrictedSpan_le_d_of_degenerate`,
   `BHW.sourceGramMatrixRank_lt_orbitThreshold_of_range_degenerate`,
   `BHW.hw_highRank_eval_range_nondegenerate`,
   `BHW.hw_highRank_eval_ker_eq_gramKernel`,
   `BHW.hw_highRank_sourceCoefficientEval_ker_eq_of_sameSourceGram`,
   `BHW.hwHighRankSpanIsometry_apply_eval`,
   `BHW.HWHighRankSpanIsometryData`,
   whose fields must include `M_eq_range`, `N_eq_range`,
   `M_nondegenerate`, and `N_nondegenerate`,
   `BHW.hw_highRank_spanIsometryData_of_sameSourceGram`,
   `BHW.complexMinkowski_wittExtension_full_of_sourceSpan`,
   `BHW.fullComplexLorentz_to_complexLorentzGroup_of_det_one`,
   `BHW.fullComplexLorentz_det_neg_reflection_fixing_sourceSpan`,
   `BHW.restrictedMinkowskiRank_eq_finrank_of_nondegenerate`,
   `BHW.sourceSpan_orthogonalComplement_nontrivial_of_proper`,
   `BHW.complexMinkowskiOrthogonalSubmodule_nondegenerate`,
   `BHW.exists_nonisotropic_in_nondegenerate_subspace`,
   `BHW.det_eq_of_conj_by_linearEquiv`,
   `BHW.det_restrict_reflection_span`,
   `BHW.det_quotient_reflection_span`,
   `BHW.det_moduleReflection_of_nonzero`,
   `BHW.fullComplexLorentzReflection`,
   `BHW.fullComplexLorentzReflection_det`,
   `BHW.fullComplexLorentzReflection_fix_subspace`,
   `BHW.sourceFullFrameDet_fullComplexLorentzAction`,
   `BHW.fullComplexLorentz_det_eq_frameMapDet_of_fullRank`,
   `BHW.sourceFullFrameBasis`,
   `BHW.sourceFullFrameBasis_apply`,
   `BHW.sourceFullFrameDet_ne_zero_of_sameGram_fullFrame`,
   `BHW.sourceFullFrameMap`,
   `BHW.sourceFullFrameMap_apply_selected`,
   `BHW.bilinForm_eq_of_basis_values`,
   `BHW.basis_pairing_zero_ext`,
   `BHW.sourceFullFrameMap_preserves_inner`,
   `BHW.sourceFullFrameMap_apply_all`,
   `BHW.sourceFullFrameMatrix_linearEquivAction`,
   `BHW.sourceFullFrameDet_linearEquivAction`,
   `BHW.det_sourceFullFrameMap_eq_ratio`,
   `BHW.sourceFullFrameDet_ratio_eq_of_sameSourceGram_fullRank`,
   `BHW.HWFullRankSameGramFrameMapDet`,
   `BHW.hwFullRankSameGramFrameMapDet_eq_det_ratio_of_fullFrame`,
   `BHW.HWSameSourceGramSOOrientationCompatible`,
   `BHW.sourceComplexMinkowskiBilinForm_isSymm`,
   `BHW.exists_complex_unit_orthogonal_basis`,
   `BHW.bilinForm_eq_sum_coords_of_unitOrthogonalBasis`,
   `BHW.nondegenerate_complexSymmetricBilinForm_linearEquiv_of_finrank_eq`,
   `BHW.exists_complexMinkowskiOrthogonalComplementIsometry`,
   `BHW.HallWightmanFullComplexLorentzGroup.ofLinearEquiv`,
   `BHW.HallWightmanFullComplexLorentzGroup.ofLinearEquiv_vectorAction`,
   `BHW.complexMinkowski_wittExtension_detOne_of_sourceSpan`,
   `BHW.complexMinkowski_wittExtension_or_improper_of_sourceSpan`,
   `BHW.HWSameSourceGramImproperOrbitData`, and
   `BHW.hw_sameSourceGram_regular_orbit_or_improper`, then
   the determinant-`1` branch uses
   `BHW.extendF_complexLorentzInvariant_of_cinv` with both `hF_holo` and
   `hF_cinv`, the determinant-`-1` full-rank branch uses
   `BHW.hallWightmanFullComplexLorentzInvariantOnExtendedTube_eq`, and the
   singular
   two-curve limit theorem
   `BHW.hw_sameSourceGram_singularLimit_extendF_eq`.  The singular data must
   expose two endpoint Lorentz-orbit curves, one from `z` and one from `w`,
   both converging to the same base configuration; value equality is then
   derived from extended-tube Lorentz invariance and continuity, not stored as
   an analytic field and not asserted as pairwise orbit equality of the two
   approximating curve values.
   The final limit argument is now Lean-pinned in generic topology form:
   from `hf : ContinuousOn f S`, `base ∈ S`, `∀ t, curve_left t ∈ S`,
   `∀ t, curve_right t ∈ S`, both curves tending to `base`, and identities
   `f (curve_left t) = f z`, `f (curve_right t) = f w`, first compose
   `(hf.continuousWithinAt hbase).tendsto` with
   `tendsto_nhdsWithin_iff.mpr ⟨hcurve_tendsto,
   Eventually.of_forall hcurve_mem⟩`; then use
   `Filter.Tendsto.congr'` to convert the two curve limits into constant
   limits and `tendsto_nhds_unique` to get
   `f z = f base = f w`.  In the Hall-Wightman branch-law proof, `f` is
   `BHW.extendF F`, `S` is `BHW.ExtendedTube d n`, continuity is
   `(BHW.extendF_holomorphicOn n F hF_holo hF_cinv).continuousOn`, and the
   two constant-value identities come from each curve's Lorentz-orbit field
   plus `BHW.extendF_complexLorentzInvariant_of_cinv`.
   The extended-tube Lorentz-invariance support theorem
   `BHW.extendF_complexLorentzInvariant_of_cinv` is now mechanically pinned:
   destruct `z ∈ ExtendedTube d n` as `z = complexLorentzAction Λ0 w0` with
   `w0 ∈ ForwardTube d n`; build the two `extendF` preimage witnesses for
   `z` and `complexLorentzAction Λ z`; unfold `extendF`; and call the checked
   `BHWCore.extendF_preimage_eq` with the equality
   `complexLorentzAction ΓL wL =
   complexLorentzAction (Λ * ΓZ) wZ`, obtained from the two chosen witnesses
   and `BHWCore.complexLorentzAction_mul`.  This is deliberately the
   `BHWCore` lemma: the production `BHW.extendF_preimage_eq` has the older
   restricted-real-invariance signature, while the scalar-source Hall-Wightman
   branch law assumes the direct complex-Lorentz invariance hypothesis.  The
   functions and domains used by `SourceScalarRepresentativeData` are
   definitionally equal to the `BHWCore` versions, so the implementation bridge
   is `change`/`simpa`, not a new theorem route.  In the final equality passed
   to `BHWCore.extendF_preimage_eq`, use
   `(congrArg (BHWCore.complexLorentzAction Λ) hΓZ).trans
   (BHWCore.complexLorentzAction_mul Λ ΓZ hex_z.choose).symm`, rather than
   unrestricted `rw [hΓZ]`, because the chosen preimage term is dependent on
   the preimage existential.  This support lemma uses `hF_cinv`, not final
   locality, PET independence, or a source scalar representative.
   `BHW.hw_sameSourceGram_fiberAlternative` itself splits into
   `BHW.hw_sameSourceGram_regular_orbit_or_improper` with
   `BHW.HWSourceGramOrbitRankAt d n z` and either a determinant-`1` orbit or
   improper full-complex-orthogonal orbit data, and
   `BHW.hw_sameSourceGram_singular_contractionData` with
   `BHW.HWSourceGramLowRankAt d n z`.  The low-rank branch must itself pass
   through the explicit isotropic residual-frame data
   `BHW.HWLowRankIsotropicNormalForm`,
   `BHW.hw_lowRank_isotropicNormalForm_of_sameSourceGram`, and
   `BHW.hw_lowRank_isotropicNormalForm_to_contractionData`; inside the
   normal-form theorem the independent scalar block is chosen by the checked
   symmetric principal-minor input
   `BHW.exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank`, not by an
   unspecified rank argument.  The low-rank proof must also expose the genuine
   linear algebra subfacts
   `BHW.hw_lowRank_selectedSpanFrame_of_sameSourceGram`,
   `BHW.sourcePrincipalGramMatrix`,
   `BHW.hw_selectedSpanCoeff`,
   `BHW.hw_selectedSpanCoeff_projection_eq`,
   `BHW.hwLemma3_selectedResidual_inner_head`,
   `BHW.hw_lowRank_residual_pairing_eq_of_sameSourceGram`,
   `BHW.hwLemma3_selectedResidual_inner_residual_eq_zero`,
   `BHW.ComplexMinkowskiTotallyIsotropicSubspace`,
   `BHW.HWLowRankSelectedSpanAlignment`,
   `BHW.hw_lowRank_selectedSpanAlignment_of_selectedSpanFrame`,
   `BHW.hw_lowRank_residualSubspaces_after_selectedAlignment`,
   `BHW.complexMinkowski_alignResidualSubspaces_to_commonIsotropicFrame`,
   `BHW.exists_coefficients_of_mem_span_finite_frame`,
   `BHW.hw_lowRank_alignedResidualFrame_of_sameSourceGram`,
   `BHW.ComplexMinkowskiNondegenerateSubspace`,
   `BHW.complexMinkowski_isotropicFrame_dualFrameIn`,
   `BHW.complexMinkowski_isotropicDualFrame_of_residualFrame`,
   `BHW.complexMinkowski_wittExtension_subspaceIsometry`,
   `BHW.complexMinkowski_isotropicContraction_partialIsometry`,
   `BHW.complexMinkowski_isotropicContractionFamily`,
   `BHW.hw_isotropicFrame_base_mem_extendedTube_of_endpoint`,
   `BHW.hw_isotropicFrame_allCoefficients_mem_extendedTube`, and
   `BHW.hw_lowRank_isotropicContraction_staysIn_extendedTube`.  The printed
   four-dimensional Hall-Wightman proof collapses the residual frame to one
   null vector in ranks one and two; the dimension-general Lean route must
   contract a finite totally isotropic frame instead.  The normal-form packet
   must store the dual isotropic frame fields used by the contraction:
   `qDual_pair_zero`, `q_dual`, `qDual_orth`, and the contraction-family
   field `contract_scale_qDual`; otherwise the Lorentz-family construction is
   hidden behind an unexplained existence theorem.  The dual-frame supplier is
   now pinned as an induction inside the nondegenerate orthogonal complement
   `N = BHW.complexMinkowskiOrthogonalSubmodule d M`: split
   `q0` from `qtail`, use linear independence to get
   `IsCompl (ℂ∙q0) (span range qtail)` in the totally isotropic span,
   construct `p0 ∈ N` by the radical-partner theorem, split the hyperbolic
   plane `span {q0,p0}`, recurse on `qtail` inside its nondegenerate
   orthogonal complement, and assemble
   `qDual 0 = p0`, `qDual (succ a) = qtailDual a`.  This keeps every dual
   vector in `Mᗮ`; no ambient dual-vector choice outside the selected-span
   orthogonal complement is allowed.  The contraction family is
   split through the standard finite-dimensional Witt lemma
   `BHW.complexMinkowski_wittExtension_subspaceIsometry`: first define the
   partial isometry on
   `span (range ξ) ⊔ span (range q) ⊔ span (range qDual)` fixing `ξ`,
   scaling `q` by `Real.exp (-t)`, and scaling `qDual` by `Real.exp t`; then
   use the dual-pairing equations to prove this partial map preserves the
   complex Minkowski form before extending it to `ComplexLorentzGroup d`.
   The tube-membership fields are sourced from Hall-Wightman's second and
   third remarks after Lemma 2:
   `BHW.hw_isotropicFrame_base_mem_extendedTube_of_endpoint` proves that
   removing an orthogonal totally isotropic finite-frame component from an
   extended-tube point leaves an extended-tube point.  The precise proof no
   longer asserts that deleting a complex null residual leaves a
   forward-tube representative; that stronger statement is false.  The proof
   instead uses the exact Hall-Wightman route: the second remark rewrites a
   forward-tube point with one orthogonal null residual as
   `η + β q`, where `η ∈ ForwardTube` and `q` has the standard real
   spacelike null normal form relative to `η`.  The blueprint now expands
   that second remark through the real/imaginary null split
   `q = qre + i qim`, exclusion of the lightlike-collinear case by
   non-orthogonality to a strict forward-cone difference, the coefficient
   projection `ξ i = η i + β i q`, and the equation-(41) cone lemma
   `forwardCone_remove_spacelikeOrthogonal_twoPlane`.  This normal-form
   packet explicitly assumes `[NeZero n]`.  The remaining finite Cauchy
   equality case inside the Lorentz-index-one null-collinearity argument is
   now pinned to a Lean-level sum-of-squares proof: define
   `xy = ∑ i, x i * y i`, `xx = ∑ i, x i ^ 2`, `yy = ∑ i, y i ^ 2`, square
   the equality hypothesis to get `xy ^ 2 = xx * yy`, expand
   `∑ i, (xy * x i - xx * y i) ^ 2` with
   `BHW.sum_sq_linear_combination_expand`, and close coordinatewise with the
   checked `BHW.sum_sq_eq_zero`.  The subsequent time-coordinate
   synchronization for `BHW.realNull_orthogonal_collinear` is likewise
   explicit: multiply the spatial relation by `x_i` and `y_i`, sum, rewrite
   with the three `minkowskiInner_decomp` identities, and cancel one nonzero
   time factor unless both null vectors are zero, which is excluded by
   `hne`.  The finite Cauchy bridge and null-collinearity theorem are now
   checked in `SourceHWTubeCoefficient.lean`.  The next positivity lemma
   `BHW.real_orthogonal_equalNorm_not_collinear_positive` is reduced to an
   exact Lean trichotomy on `A = MinkowskiSpace.minkowskiInner d x x`: the
   zero branch calls the checked null-collinearity theorem, and the negative
   branch applies
   `MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg` to `x` or
   `-x` according to the sign of the time component.  This positivity lemma is
   now checked in `SourceHWTubeCoefficient.lean`, as is
   `BHW.realImag_null_not_collinear_to_spacelike_orthonormal`, whose scaling
   proof normalizes by `s = sqrt A` and factors `1 / s^2` through the finite
   Minkowski sums with `Finset.sum_div`.  The forward-tube complex-null
   normal form
   `BHW.complexNullOrthogonal_forwardTube_spacelikeNormalForm` is also
   checked, after the real-null forward-cone contradiction theorem it uses
   to exclude the lightlike-collinear alternative.  No untracked Hilbert-space
   equality-case theorem is being hidden here.  The `n = 0` case is a separate
   trivial empty-configuration branch and cannot be used to infer spacelike
   normal form for an arbitrary null vector.  The equation-(41) cone-removal
   lemma `BHW.forwardCone_remove_spacelikeOrthogonal_twoPlane` is checked as
   well; its path-square expansion uses the existing bilinearity lemmas for
   `MinkowskiSpace.minkowskiInner` and a local conversion to the
   `BHW.InOpenForwardCone` quadratic-sum convention.  The coefficient split
   `BHW.hw_secondRemark_coefficients_orthogonalTo_nullPlane` is checked after
   explicitly complexifying the real spacelike directions to `U,V` and casting
   their real inner-product identities into `sourceComplexMinkowskiInner`.
   The third remark is
   expanded through the explicit complex two-plane rotation
   `complexMinkowski_twoPlaneComplexRotation_lorentz`: fix the orthogonal
   complement of `span {u,v}` and act on the plane by
   `u ↦ cosh t u + i sinh t v`,
   `v ↦ -i sinh t u + cosh t v`, which preserves the complex Minkowski form
   and scales `u + i v` by `exp t`.  This gives all coefficient choices in
   `ExtendedTube`.  A finite induction over the residual frame gives
   `BHW.hw_isotropicFrame_allCoefficients_mem_extendedTube`.
   This membership theorem needs only `q_pair_zero` and `q_orth`; the dual
   frame data `qDual_pair_zero`, `q_dual`, and `qDual_orth` are required
   later for the null-boost contraction family and the singular value-limit
   argument, not for coefficient-freedom membership.
   `BHW.hw_isotropicFrame_allCoefficients_mem_extendedTube` then proves that
   once one coefficient tuple along the frame lies in the extended tube, every
   coefficient tuple along that frame does, including the zero tuple.  The
   blueprint now expands the latter theorem into its actual Lean steps:
   prove the one-null-vector coefficient theorem from the second and third
   remarks, transport an arbitrary extended-tube endpoint to a forward-tube
   representative, and finite-induct over the residual frame.  Thus
   `base_mem`,
   `contracted_left_mem`, and `contracted_right_mem` are theorem outputs, not
   assumptions and not consequences of closedness of the open extended tube.
   The selected-span step is now checked in
   `SourceHWSelectedProjection.lean`.  The coefficients are the inverse
   principal-Gram-block formula
   `hw_selectedSpanCoeff n r I G i = row_i(G) * A⁻¹`, where
   `A = sourcePrincipalGramMatrix n r I G`; residual orthogonality is the
   finite identity `row_i * A⁻¹ * A = row_i`.  The checked residual-pairing
   bridge derives `hI : Function.Injective I` from `hminor` by
   `BHW.sourceMatrixMinor_ne_zero_left_injective`, obtains the upper-left
   unit from `BHW.isUnit_selectedIndexSumEquiv_toBlocks₁₁_det`, identifies
   complementary residual pairings with `BHW.reindexedRectSchurComplement` by
   `BHW.hwLemma3_selectedComplement_residual_inner_residual_eq_schur`, and
   kills them using
   `BHW.rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero`.  The
   resulting checked theorem
   `BHW.hwLemma3_selectedResidual_inner_residual_eq_zero` is indexed over all
   original labels, with selected cases closed by
   `BHW.hwLemma3_selectedResidual_selected`.  The same file also checks
   `BHW.hwLemma3_selectedProjection_gram_eq` and
   `BHW.hwLemma3_selectedProjection_span_finrank_eq_rank`, so the selected
   projection tuple is a same-Gram adapted-rank representative once the
   extended-tube membership of the zero-residual coefficient choice is proved.
   The common residual frame is a separate two-stage Witt-geometric theorem:
   `BHW.hw_lowRank_selectedSpanAlignment_of_selectedSpanFrame` first builds
   the Lorentz transform aligning the selected `z` span with the selected `w`
   span, and only then
   `BHW.hw_lowRank_residualSubspaces_after_selectedAlignment` builds the two
   totally isotropic residual spans in the common orthogonal complement.  This
   order is mandatory; before the selected-span Lorentz alignment there is no
   common selected subspace in which the residual statement is true.  Then
   `BHW.complexMinkowski_alignResidualSubspaces_to_commonIsotropicFrame`
   supplies a Lorentz transformation fixing the selected span and placing the
   two residual families in one finite totally isotropic frame `q`, and
   `BHW.exists_coefficients_of_mem_span_finite_frame` extracts the coefficient
   functions `aLeft` and `aRight` from the explicit span-membership fields.
   The residual-frame alignment now has an implementation-level support
   packet in the blueprint: define
   `BHW.complexMinkowskiOrthogonalSubmodule d M`; prove its nondegeneracy
   from nondegeneracy of `M`; build a maximal isotropic frame in that
   orthogonal complement extending the right residual subspace `Rw`; inject
   the left residual subspace `Rz` into the span of that frame by the
   Witt-index dimension bound; then define the partial isometry on
   `M ⊔ Rz` as the identity on `M` and that injection on `Rz`, with codomain
   `M ⊔ LinearMap.range Eleft`.  The blueprint now pins the missing
   direct-sum proof: `BHW.complexMinkowski_disjoint_of_nondegenerate_orthogonal`
   gives `Disjoint M Rz` and `Disjoint M (LinearMap.range Eleft)`, because an
   intersection vector lies in `M` and is orthogonal to every vector of `M`;
   `BHW.span_frame_orthogonal_to_subspace` transports pointwise
   frame-orthogonality to the whole span containing `Eleft x`.  The helper
   `BHW.directSum_identity_sum_isotropicEmbedding` is therefore a genuine
   linear equivalence of the two sup submodules, and its preservation theorem
   is the explicit block-pairing calculation.  This correction is important:
   the map from `Rz` is only an injective isometry into the frame span, not an
   equivalence onto the whole maximal frame span, and the frame must be chosen
   to contain `Rw` before Witt extension is applied.
   The later convergence proof must use the explicit contracted
   configurations and `Real.tendsto_exp_neg_atTop_nhds_zero`, not continuity
   of a noncomputably chosen `t ↦ contract t`.  The contraction data
   consists of two Lorentz-orbit curves, one from each endpoint, converging to
   the same base configuration; it is not a claim that the two approximating
   curve values are pairwise in one orbit.  The proof of those orbit fields
   uses `BHW.complexLorentzAction_mul` for the left curve
   (`N.contract t * N.Λ0`) and the direct `N.contract t` action for the right
   curve.  The analytic value equality is proved only later by Lorentz
   invariance plus continuity.
   `BHW.SourceComplexGramRegularAt` remains reserved for the later local
   source-Gram image theorem; it is not the Hall-Wightman Lemma-2 predicate.
   The arithmetic support for this split is mechanical and should not be
   counted as a Hall-Wightman theorem: after unfolding
   `HWSourceGramLowRank` and `HWSourceGramOrbitRank`,
   `hwSourceGram_lowRank_iff_not_orbitRank` is `Nat.lt_of_not_ge` and
   `not_lt_of_ge`; the analogous
   `hwSourceGram_exceptionalRank_iff_not_maxRank` proves the local-chart
   max-rank complement; and
   `hwSourceGramOrbitRankAt_of_sourceGram_eq` is `simpa` from the displayed
   equality of `sourceMinkowskiGram` values.  Thus the first genuine
   mathematical branch-law obligations are the high-rank span-isometry/Witt
   extension and the low-rank isotropic contraction packet, not the
   predicate split itself.
   The high-rank nondegeneracy proof now has an explicit rank bridge:
   `sourceGramMatrixRank_eq_restrictedMinkowskiRank_range` identifies the
   scalar Gram matrix rank with the rank of the complex Minkowski form
   restricted to the span generated by the source vectors.  Its proof is
   split into the finite-matrix rank identification for
   `sourceCoefficientGramMap`, the equality between the scalar Gram kernel
   and the preimage of the restricted Minkowski radical under
   `sourceCoefficientEval`, and the quotient rank-nullity computation through
   `sourceCoefficientEval.quotKerEquivRange`.  The proof-local helpers
   `scalarGramKernel_quot_equiv_restrictedRadical` and
   `finrank_range_eq_sub_finrank_ker_of_rank_nullity` may be used, but they
   only expose quotient/rank-nullity bookkeeping and are not new route
   surfaces: the quotient map is `Submodule.liftQ`, and the exact APIs are
   `Submodule.range_liftQ`, `Submodule.ker_liftQ`, and
   `LinearMap.finrank_range_add_finrank_ker`.  Separately,
   `sourceGramMatrixRank_lt_orbitThreshold_of_range_degenerate` proves that a
   nonzero restricted radical forces scalar rank below `min d n`.  That
   rank-drop theorem is decomposed into explicit finite-dimensional support:
   degeneracy gives positive restricted-radical finrank; positive radical
   finrank gives `restrictedMinkowskiRank d M < finrank M`; the source span
   has finrank `<= n`; and a degenerate restricted subspace is proper in the
   `(d + 1)`-dimensional ambient space, so its finrank is `<= d`.  The exact
   APIs are `Submodule.one_le_finrank_iff`, `Submodule.finrank_le`,
   `LinearMap.finrank_range_le`, `Submodule.finrank_lt`,
   `Module.finrank_fin_fun`, and the checked ambient nondegeneracy
   `BHW.sourceComplexMinkowskiInner_left_nonDegenerate`; the final arithmetic
   is `omega`/`Nat.lt_succ_iff`.  This prevents the direct-orbit branch from
   silently replacing Hall-Wightman's scalar-rank condition by a source-map
   regularity or span-nondegeneracy assumption.
   The coefficient-kernel transport now has checked Lean support for its
   first finite algebra layer in
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceCoefficient.lean`:
   `BHW.sourceCoefficientGramMap` is the explicit linear map
   `a ↦ (j ↦ ∑ i, a i * G i j)`, its kernel is
   `BHW.sourceCoefficientGramKernel`, and the finite algebra lemma
   `BHW.sourceCoefficientGramMap_apply_sourceMinkowskiGram` identifies each
   coordinate with
   `BHW.sourceComplexMinkowskiInner d (sourceCoefficientEval d n z a) (z j)`
   using the already-checked
   `sourceComplexMinkowskiInner_sum_smul_left` and
   `sourceMinkowskiGram_apply_eq_complexInner`.  Then
   `BHW.sourceCoefficientEval_ker_le_gramKernel` is the immediate `mem_ker`
   consequence.  The reverse finite test uses
   `BHW.sourceCoefficientEval_single`, and
   `BHW.sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero` turns the
   scalar Gram kernel into the exact all-range orthogonality predicate needed
   for the restricted radical.  The checked
   `BHW.sourceCoefficientEval_pair_eq_sum_gram` also records that pairings of
   coefficient-evaluated source vectors depend only on the source Gram matrix.
   The finite-matrix identification
   `BHW.sourceCoefficientGramMap_eq_toLin_transpose` is also checked; it pins
   the coefficient Gram map to `Matrix.toLin' Gᵀ`.  The restricted form
   definitions `BHW.restrictedMinkowskiLeftMap`,
   `BHW.restrictedMinkowskiRadical`, and `BHW.restrictedMinkowskiRank` are
   checked in `BHWPermutation/SourceRank.lean`, as is the subtype/range
   membership bridge
   `BHW.sourceCoefficientEval_mem_restrictedMinkowskiRadical_iff`: unfold
   `restrictedMinkowskiRadical`, apply the restricted left map to
   `⟨evalZ b, ⟨b, rfl⟩⟩`, and conversely destruct an arbitrary
   `y : LinearMap.range evalZ` as `⟨_, b, rfl⟩`.  The scalar Gram kernel
   preimage theorem `BHW.sourceCoefficientGramKernel_eq_eval_preimage_radical`
   is now checked as well.  The matrix-rank entry
   `BHW.sourceGramMatrixRank_eq_finrank_range_sourceCoefficientGramMap` is
   checked by combining the transpose identification with
   `Matrix.rank_transpose`, `Matrix.rank_eq_finrank_range_toLin`, and
   `Matrix.toLin_eq_toLin'`.  The remaining quotient bridge must now apply
   rank-nullity on `ker evalZ` and identify the quotient radical with the
   restricted radical.  Thus
   `BHW.restrictedMinkowskiLeftMap` itself is no longer an abstract
   placeholder in the blueprint: it is the explicit linear map
   `x ↦ (y ↦ sourceComplexMinkowskiInner d x y)`, with linearity discharged by
   `sourceComplexMinkowskiInner_add_left/right` and
   `sourceComplexMinkowskiInner_smul_left/right`.
   `BHW.hw_highRank_sourceCoefficientEval_ker_eq_of_sameSourceGram` rewrites
   both evaluation kernels through the common
   `sourceCoefficientGramKernel` and transports the orbit-rank hypothesis
   from `z` to `w` by `BHW.hwSourceGramOrbitRankAt_of_sourceGram_eq`.  Thus
   the quotient map from coefficient classes to
   `LinearMap.range (sourceCoefficientEval ...)` is well-defined only after
   the checked kernel equalities, not by the informal assignment
   `z i ↦ w i`.
   The quotient-induced span isometry is now Lean-shaped as well:
   `BHW.hwHighRankSpanIsometry_apply_eval` proves that the constructed map
   sends `⟨evalZ a, ⟨a, rfl⟩⟩` to `⟨evalW a, ⟨a, rfl⟩⟩` using
   `LinearMap.quotKerEquivRange_symm_apply_image`,
   `LinearMap.quotKerEquivRange_apply_mk`, and
   `Submodule.quotEquivOfEq_mk`; preservation of the pairing is reduced to
   `BHW.sourceCoefficientEval_pair_eq_sum_gram` and the common Gram equality.
   The high-rank branch is equally not allowed to skip directly from equal
   Gram entries to a Lorentz transform: the proof must first identify the
   coefficient kernels of the two source tuples through the common scalar
   Gram kernel, descend the identity map on coefficient space to an isometry
   of the two vector spans, and only then apply the determinant-sensitive
   extension alternative
   `BHW.complexMinkowski_wittExtension_detOne_of_sourceSpan` /
   `BHW.complexMinkowski_wittExtension_or_improper_of_sourceSpan`.

   Lemma-2 readiness is now componentwise.  The branch law may move to Lean
   only after the following rows have proof terms or checked local support:

   | Subpacket | Status | Proof obligation |
   | --- | --- | --- |
   | Rank split predicates and complement lemmas | Implemented and exact-file checked in `BHWPermutation/SourceRank.lean`; umbrella import checked in `BHWPermutation.lean`. | Defines `sourceGramMatrixRank`, `sourceConfigGramMatrixRank`, `HWSourceGramOrbitRank`, `HWSourceGramLowRank`, `HWSourceGramOrbitRankAt`, `HWSourceGramLowRankAt`, `HWSourceGramMaxRank`, `HWSourceGramExceptionalRank`, `HWSourceGramMaxRankAt`, and `HWSourceGramExceptionalRankAt`; proves complement and same-Gram transport lemmas. |
   | Coefficient maps and scalar Gram kernel | Implemented and exact-file checked in `BHWPermutation/SourceCoefficient.lean`; umbrella import checked in `BHWPermutation.lean`. | Defines `sourceCoefficientEval`, `sourceCoefficientGramMap`, and `sourceCoefficientGramKernel`; proves `sourceCoefficientGramMap_apply_sourceMinkowskiGram`, `sourceCoefficientEval_single`, `sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero`, `sourceCoefficientEval_pair_eq_sum_gram`, and `sourceCoefficientEval_ker_le_gramKernel`. |
   | Restricted-rank bridge | Implemented and exact-file checked in `BHWPermutation/SourceRank.lean`. | The checked proof identifies scalar matrix rank with `finrank (range sourceCoefficientGramMap)`, quotients coefficient space by `ker sourceCoefficientEval` using `Submodule.liftQ` and `Submodule.range_liftQ`, identifies the lifted kernel with the restricted radical through `sourceCoefficientEval.quotKerEquivRange`, applies `LinearMap.finrank_range_add_finrank_ker`, and assembles `sourceGramMatrixRank_eq_restrictedMinkowskiRank_range`. |
   | High-rank kernel transport | Implemented and exact-file checked in `BHWPermutation/SourceRank.lean`. | Defines `ComplexMinkowskiNondegenerateSubspace`; proves that a degenerate restricted span has positive radical finrank, hence restricted rank below span dimension, span dimension `<= n` and `<= d`, scalar rank `< min d n`, high-rank span nondegeneracy, `ker evalZ = gramKernel`, and same-Gram transport `ker evalZ = ker evalW`. |
   | High-rank span isometry data | Implemented and exact-file checked in `BHWPermutation/SourceRank.lean`. | Constructs the quotient-induced isometry as `hwHighRankSpanIsometryOfKernelEq`, proves `hwHighRankSpanIsometry_apply_eval`, packages `HWHighRankSpanIsometryData` by `hw_highRank_spanIsometryData_of_sameSourceGram`, and proves `HWHighRankSpanIsometryData_sourceGram_eq`.  This closes the well-defined coefficient-quotient part before any Witt extension. |
   | High-rank determinant/Witt orbit theorem | Full transcript pinned; production Lean not started. | Starting from `HWHighRankSpanIsometryData`, split the Witt extension into determinant-`1` proper orbit and determinant-`-1` improper full-complex-orthogonal orbit.  The full-complex extension now decomposes through source span plus orthogonal complement, complement-isometry classification over `ℂ`, product assembly, and conversion from inner-preserving linear equivalence to `HallWightmanFullComplexLorentzGroup`; the classification proof is pinned by orthogonal bases, complex square-root normalization, and the coordinate-sum identity.  The full-frame determinant ratio is pinned by the unique selected-frame isometry, same-Gram extension from the selected full frame to all source vectors, and determinant action on frame matrices.  The proper-span determinant repair decomposes through `sourceSpan_orthogonalComplement_nontrivial_of_proper`, nonisotropic-vector polarization, and the Householder/module-reflection determinant via line-plus-quotient.  The final public orbit and orbit-or-improper theorems only assemble the span-isometry data, consume the appropriate determinant-sensitive Witt producer, and rewrite vectorwise action equality to configuration equality.  No theorem-shape gap remains in this high-rank row; the conditional pure-Gram fork still needs Hall-Wightman's space-inversion/improper-component source input. |
   | Low-rank selected principal block and residual frame | Checked in `BHWPermutation/SourceHWSelectedProjection.lean`; principal-minor extraction checked locally. | The checked layer defines `sourcePrincipalGramMatrix`, `hw_selectedSpanCoeff`, `hwLemma3_selectedProjection`, and `hwLemma3_selectedResidual`; proves selected rows are fixed, `row_i * A⁻¹ * A = row_i`, selected/projection-residual orthogonality, the complementary residual-Schur entry theorem, rank-`r` residual-residual zero, original/residual orthogonality, projection Gram equality, projected-span finrank `r`, explicit finite-frame coordinates for span membership, and `hwLemma3_selectedResidual_isotropicFrameData`.  Remaining low-rank work starts at extended-tube coefficient freedom and the two-endpoint residual alignment theorem, not selected Schur algebra. |
   | Low-rank residual-frame alignment | Proof transcript pinned; production Lean not started. | Align selected spans first, extract the residual span, choose an independent common isotropic frame `q`, store explicit coefficient functions for both residual families, and prove pairwise isotropy plus orthogonality to the selected block from the zero Schur complement. |
   | Dual frame and contraction family | Proof transcript pinned; production Lean not started. | Store `qDual_pair_zero`, `q_dual`, `qDual_orth`, build the finite partial boost scaling `q`/`qDual`, and Witt-extend it; the dual frame is used only for null-boost contraction and the two-curve value equality/limit, not for the coefficient-freedom membership theorem. |
   | Tube stability and singular limit | Checked in `BHWPermutation/SourceHWTubeCoefficient.lean`; corrected target for arbitrary endpoints is `ExtendedTube`, not `ForwardTube`. | The checked layer now runs through Hall-Wightman's second and third remarks, the explicit determinant-one complex Lorentz two-plane rotation, the arbitrary-endpoint one-null coefficient theorem, the finite-frame induction, the `n = 0` wrapper, and the public base/all-coefficients theorem `BHW.hw_isotropicFrame_allCoefficients_mem_extendedTube`.  It also records `complexLorentzAction_inv_left`, `complexLorentzVectorAction_inv_left`, and `sourceComplexMinkowskiInner_finset_sum_smul_right` as the Lean bridge lemmas needed by the transport and induction steps.  The dual frame remains only for the later null-boost contraction/value-limit packet, not for coefficient-freedom membership. |
   | `extendF_complexLorentzInvariant_of_cinv` | Implemented and exact-file checked in `ComplexInvariance/Extend.lean`. | Unfold `extendF`, choose forward-tube preimages, and use the new direct-preimage helper `BHW.extendF_preimage_eq_of_cinv`; no PET/EOW/locality and no scalar-representative content. |

   The oriented max-rank continuation layer consumes the following public
   corollary of the determinant/Witt row:

   ```lean
   theorem BHW.hw_sameSourceOrientedInvariant_maxRank_properOrbit
       [NeZero d] (hd : 2 <= d)
       (n : Nat)
       {z w : Fin n -> Fin (d + 1) -> ℂ}
       (hzmax :
         BHW.SourceOrientedMaxRankAt d n
           (BHW.sourceOrientedMinkowskiInvariant d n z))
       (hinv :
         BHW.sourceOrientedMinkowskiInvariant d n z =
           BHW.sourceOrientedMinkowskiInvariant d n w) :
       ∃ Λ : ComplexLorentzGroup d,
         w = BHW.complexLorentzAction Λ z
   ```

   Its proof unfolds the oriented invariant into ordinary same-Gram equality
   plus equality of all selected full-frame determinants.  The ordinary
   same-Gram equality supplies `HWHighRankSpanIsometryData`.  If the source
   span is proper, determinant repair gives a determinant-`1` extension
   directly.  If the source span is all of spacetime, choose any selected
   full frame with nonzero determinant from `hzmax`; the determinant action
   formula and `hinv` force the full-frame extension determinant to be `1`,
   excluding the improper branch.  Convert the determinant-`1` full
   Lorentz element to `ComplexLorentzGroup d` and rewrite the vectorwise
   action equality to the displayed configuration equality.

   Therefore, after the theorem-2 proof-doc gate is fully closed, the first
   remaining Lean target in this block is now the high-rank
   determinant/Witt-extension support theorem above, not the final branch-law wrapper
   `BHW.extendedTube_same_sourceGram_extendF_eq`.  This sentence is not
   permission to start production Lean while the oriented scalar-source producer ledger above
   remains open.
2. `BHW.sourceExtendedTubeGramDomain_relOpen_connected`: the scalar image
   `BHW.sourceExtendedTubeGramDomain d n` is relatively open in
   `BHW.sourceComplexGramVariety d n` and connected.  Continuity of the Gram
   map is not enough for relative openness; this is the BHW scalar-product
   geometry of `S'_n`.  The connectedness half can use the checked
   `BHW.isConnected_extendedTube` and
   `(BHW.contDiff_sourceMinkowskiGram d n).continuous`; the relative-openness
   half is the Hall-Wightman scalar-neighborhood theorem.
   The connectedness proof is now Lean-pinned: set
   `hGram_cont := (BHW.contDiff_sourceMinkowskiGram d n).continuous`, take
   `(BHW.isConnected_extendedTube (d := d) (n := n)).image
   (BHW.sourceMinkowskiGram d n) hGram_cont.continuousOn`, and finish by
   `simpa [BHW.sourceExtendedTubeGramDomain]`.  The declaration
   `BHW.contDiff_sourceMinkowskiGram` lives in
   `BHWPermutation/SourceComplexChart.lean`; a future scalar-representative
   implementation must import that existing file or place the connectedness
   theorem downstream of it, rather than duplicating the continuity proof in
   `SourceExtension.lean`.  Thus the only
   non-mechanical content in this theorem is the relative-openness line
   `BHW.sourceExtendedTubeGramDomain_relOpen`, whose proof is the Lemma-3
   local-realization packet below.
   The assembly from the pointwise Lemma-3 form to the relative-open theorem
   is now Lean-pinned: first make the point `Z` explicit by setting
   `hLocal := fun Z hZ =>
   BHW.sourceExtendedTubeGramDomain_relOpen_at (d := d) hd (n := n) hZ`;
   then `choose O hO_open hZO hO_sub using hLocal`, take the ambient open set
   `⋃ Z : {Z // Z ∈ sourceExtendedTubeGramDomain d n}, O Z.1 Z.2`, prove it
   open by `isOpen_iUnion`, prove the forward inclusion by
   `Set.mem_iUnion.mpr ⟨⟨W,hWdomain⟩, hZO W hWdomain⟩` plus
   `BHW.sourceExtendedTubeGramDomain_subset_sourceComplexGramVariety`, and
   prove the reverse inclusion by `Set.mem_iUnion.mp` followed by
   `hO_sub Z.1 Z.2 ⟨hWO,hWvar⟩`.  Choosing directly from a theorem with
   implicit `Z` gives an inconvenient proof-indexed family, so the explicit
   `hLocal` line is part of the intended Lean proof.
   The local form is
   `BHW.sourceExtendedTubeGramDomain_relOpen_at`; its implementation is the
   Hall-Wightman Lemma-3 realization theorem
   `BHW.hwLemma3_sourceGram_localVectorRealization`: choose an extended-tube
   realization `z0` of the scalar point, then first replace it by the
   adapted same-Gram representative supplied by
   `BHW.hwLemma3_extendedTube_adaptedRankRepresentative`.  This adapted
   representative is still in the ordinary extended tube and has
   source-vector span dimension equal to the scalar Gram rank.  This
   replacement is mandatory: an invertible source-coordinate change cannot
   kill nonzero radical tail vectors of an arbitrary representative.  The
   low-rank construction of the adapted representative is sourced from the
   Hall-Wightman Lemma-2 residual-frame theorem plus
   `BHW.hw_isotropicFrame_allCoefficients_mem_extendedTube`, setting the null
   residual coefficients to zero while preserving scalar products.  The proof
   is now checked in
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtendedTubeRank.lean`
   through
   `BHW.sourceGramMatrixRank_pos_of_mem_extendedTube`,
   with its support theorem
   `BHW.openForwardCone_imag_complexSelfInner_ne_zero`: if
   `v = x + iη` and `η ∈ BHW.InOpenForwardCone d`, then `B(v,v) ≠ 0`
   because `BHW.sourceComplexMinkowskiInner_self_re_im` turns `B(v,v)=0`
   into both `B(x,η)=0` and `B(x,x)=B(η,η)`, while
   `MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg` gives
   `0 ≤ B(x,x)` and the checked open-cone/timelike conversion gives
   `B(η,η) < 0`; a nonzero forward-tube diagonal Gram entry then gives
   positive matrix rank by
   `BHW.matrix_rank_pos_of_nonzero_entry`, and the extended-tube case follows
   by `BHW.sourceMinkowskiGram_complexLorentzAction`.  The selected principal
   block coefficient/projection layer is now checked in
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceHWSelectedProjection.lean`:
   `BHW.sourcePrincipalGramMatrix`,
   `BHW.sourcePrincipalGramMatrix_det_isUnit_of_sourceMatrixMinor_ne_zero`,
   `BHW.hw_selectedSpanCoeff`,
   `BHW.hw_selectedSpanCoeff_projection_eq`,
   `BHW.hw_selectedSpanCoeff_selected`,
   `BHW.hwLemma3_selectedProjection`,
   `BHW.hwLemma3_selectedResidual`,
   `BHW.hwLemma3_selectedProjection_selected`,
   `BHW.hwLemma3_selectedProjection_inner_head`,
   `BHW.hwLemma3_selectedResidual_inner_head`,
   `BHW.hwLemma3_selectedResidual_head_inner`,
   `BHW.hwLemma3_selectedResidual_selected`,
   `BHW.hwLemma3_selectedProjection_inner_residual`,
   `BHW.hwLemma3_selectedResidual_inner_projection`,
   `BHW.hwLemma3_selectedComplement_residual_inner_residual_eq_schur`,
   `BHW.hwLemma3_selectedResidual_inner_residual_eq_zero`,
   `BHW.hwLemma3_selectedProjection_add_residual`,
   `BHW.hwLemma3_selectedResidual_inner_original_eq_zero`,
   `BHW.hwLemma3_original_inner_selectedResidual_eq_zero`,
   `BHW.hwLemma3_selectedProjection_gram_eq`,
   and `BHW.hwLemma3_selectedProjection_span_finrank_eq_rank`.  This checks
   the inverse principal-block cancellation `row_i * A⁻¹ * A = row_i`,
   selected residual orthogonality, indexed residual-residual Schur zero, the
   projected same-Gram equation, and the projected source-span rank.  The
   finite residual-frame support theorem is also checked:
   `BHW.hwLemma3_selectedResidual_isotropicFrameData` applies
   `Submodule.exists_fun_fin_finrank_span_eq` to the residual span, uses the
   returned membership in `Set.range residual` to inherit residual-residual
   zero and projection-residual orthogonality, uses
   `BHW.exists_coefficients_of_mem_span_finite_frame` to produce the
   coefficient functions, and closes the source decomposition with
   `BHW.hwLemma3_selectedProjection_add_residual`.  The remaining adapted
   representative construction now starts at the Hall-Wightman
   all-coefficients extended-tube theorem with zero coefficients.  The
   theorem-2 blueprint now expands the adapted quantitative theorem down to
   Hall-Wightman's actual Lemma-3 algebra:
   `BHW.hwLemma3_selectedBlock_sqrt_near_identity` for the analytic square
   root of the selected principal block near `1`; this is now pinned to a
   fully decomposed finite matrix binomial series packet under
   `open scoped Matrix.Norms.Operator`, with imports
   `Mathlib.Analysis.Analytic.Binomial`,
   `Mathlib.Analysis.Matrix.Normed`,
   `Mathlib.Analysis.Normed.Ring.InfiniteSum`, and
   `Mathlib.Topology.Instances.Matrix`.  The `r = 0` selected-block case is
   separated as a vacuous empty-matrix branch.  For `0 < r`, the support
   layer defines
   `matrixSqrtOneAddNearZero r B =
   ∑' m, Ring.choose (1/2 : ℂ) m • B^m` and proves scalar binomial
   coefficient summability from `binomialSeries_radius_ge_one`, matrix-term
   absolute summability by `norm_pow_le`, the Cauchy-product square identity
   by
   `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, and the
   coefficient convolution by `Ring.add_choose_eq`.  The transpose step is
   pinned to `Matrix.transpose_tsum`, `Matrix.transpose_smul`, and
   `Matrix.transpose_pow`; continuity at zero is isolated as the genuine
   Banach-algebra theorem `BHW.scalarPowerSeries_tendsto_at_zero`; and the
   final entrywise smallness uses
   `BHW.matrix_opNorm_le_card_mul_sup_entry`,
   `BHW.matrix_norm_lt_of_entry_bound`, and
   `BHW.matrix_entry_norm_le_linfty_opNorm`,
   `BHW.hwLemma3_schurComplement_rank_bound` for the lower-right residual
   rank `<= d + 1 - r`; this is now pinned to Mathlib's actual
   `Matrix.fromBlocks_eq_of_invertible₁₁` from
   `Mathlib.LinearAlgebra.Matrix.SchurComplement`.  The proof converts
   `⅟A` to `A⁻¹` via `Matrix.invertibleOfIsUnitDet` and
   `Matrix.invOf_eq_nonsing_inv`, drops the two block-triangular factors by
   `Matrix.isUnit_fromBlocks_zero₁₂`,
   `Matrix.isUnit_fromBlocks_zero₂₁`,
   `Matrix.isUnit_iff_isUnit_det.mp`,
   `Matrix.rank_mul_eq_right_of_isUnit_det`, and
   `Matrix.rank_mul_eq_left_of_isUnit_det`, then proves the block-diagonal
   rank theorem
   `BHW.matrix_rank_fromBlocks_zero_zero` via
   `Matrix.rank_eq_finrank_range_toLin`,
   `LinearMap.toMatrix_prodMap`, `LinearMap.range_prodMap`, and
   `Module.finrank_prod`.  The final arithmetic is
   `Nat.le_sub_of_add_le`; symmetry of the selected block is available
   upstream but is not used by the rank algebra,
   `BHW.complexSymmetric_takagi_rankLE` and
   `BHW.complexSymmetric_factorSmall_rankLE` for the finite-dimensional
   Takagi/Bargmann factorization and its small-factor estimate; the actual
   implementation route now factors through
   `BHW.complexSymmetric_autonneTakagi_entryL1`, obtained from
   the Autonne-Takagi theorem with unitary matrix, nonnegative singular
   values, rank support, and the explicit entry-sum bound
   `‖A i a‖ <= Real.sqrt (BHW.matrixEntryL1Bound m S)`, where
   `matrixEntryL1Bound m S = ∑ p : Fin m × Fin m, ‖S p.1 p.2‖`.
   This deliberately avoids relying on any ambient matrix norm instance.  The
   finite entry-size reducer is checked in
   `BHWPermutation/SourceComplexSmallFactor.lean`:
   `matrixEntryL1Bound_nonneg`,
   `matrixEntryL1Bound_lt_of_entry_bound`,
   `exists_pos_mul_sqrt_lt`,
   `real_sqrt_lt_of_lt_mul_bound`,
   `takagiConjugateLinearMap`,
   `takagiConjugateLinearMap_add`,
   `takagiConjugateLinearMap_smul`,
   `takagiConjugateLinearMap_sq`,
   `takagiConjugateLinearMap_commutes_square`,
   `takagiConjugateLinearMap_mem_eigenspace`,
   `takagiConjugateLinearMap_conjTranspose_mulVec_eq_star`,
   `takagiConjugateLinearMap_zero_eigenspace_eq_zero`,
   `takagiHermitianSquare_isHermitian`,
   `takagiHermitianSquare_spectralTheorem`,
   `takagiHermitianSquare_eigenvalue_nonneg`,
   `takagiHermitianSquare_singularValue_nonneg`,
   `takagiHermitianSquare_eigenvalue_rankSupport`,
   `takagiHermitianSquare_singularValue_rankSupport`,
   `matrix_unitary_entry_norm_le_one`,
   `matrix_unitary_entry_mul_real_sqrt_norm_le_sqrt`,
   `complexSymmetric_takagi_factor_from_supportEmbedding`,
   `complexSymmetric_entryL1_of_takagiDiagonalData`,
   `complexSymmetric_entryL1_of_takagiDiagonalData_rankSupport`,
   `complexSymmetric_factorSmall_rankLE_of_entryL1`, and
   `sourceComplexSymmetric_factorSmall_rankLE_of_entryL1`.  Thus the small
   factor theorem no longer has a hidden estimate step.  The checked Autonne support now proves
   that the conjugate-linear map `v ↦ S.mulVec (star v)` squares to the
   positive Hermitian map `S * Sᴴ`, commutes with that square, maps each real
   eigenspace to itself, kills the zero eigenspace, and supplies the
   Hermitian-square spectral theorem plus nonnegative singular-value
   rank-support identity.  The positive-eigenspace phase step is now checked
   separately in `BHWPermutation/SourceComplexTakagiPhase.lean`.  It uses
   `EuclideanSpace ℂ (Fin m)`, not raw functions with the product/sup norm,
   defines `BHW.takagiHermitianEigenspace`, proves the Euclidean norm-square
   and norm identities for `v ↦ S.mulVec (star v)` on each eigenspace, and
   bundles the normalized positive-eigenvalue map as
   `BHW.takagiPositiveEigenspaceConjugation`.  It also checks the local
   fixed-basis objects and column equations needed by the final ONB assembly:
   `BHW.takagiPositiveEigenspaceFixedBasis`,
   `BHW.takagiPositiveEigenspaceFixedBasis_fixed`,
   `BHW.takagiConjugateLinearEuclideanMap_eq_sqrt_smul_of_positive_fixed` for
   fixed vectors in positive eigenspaces,
   `BHW.takagiPositiveEigenspace_fixedBasis_col_eigen` for the selected
   positive-eigenspace fixed basis,
   `BHW.takagiConjugateLinearEuclideanMap_zero_eigenspace_eq_zero` for the
   zero eigenspace, and `BHW.takagiZeroEigenspace_col_eigen` for the
   zero-eigenspace column equation with singular value `0`.  The fixed-basis real-form layer
   is checked in
   `BHWPermutation/SourceComplexTakagiFixed.lean`: it defines the real fixed
   submodule `BHW.conjugationFixedSubmodule`, installs the induced real inner
   product and finite-dimensional instances, proves the antiunitary identity
   `BHW.conjugateLinearIsometry_inner_map_map`, proves the explicit real-linear
   decomposition `x = (x + Jx)/2 + I • (I • (Jx - x)/2)`, proves
   injectivity and surjectivity of `(p,q) ↦ p + I • q`, bundles this as the
   real-linear equivalence `BHW.conjugationFixedPairLinearEquiv`, deduces
   `finrank ℝ fixed = finrank ℂ E` from `Module.finrank_prod` and
   `finrank_real_of_complex`, and constructs
   `BHW.conjugationFixedComplexOrthonormalBasis`, with checked pointwise
   fixedness `BHW.conjugationFixedComplexOrthonormalBasis_fixed`.  The global
   finite-dimensional collection step is now checked in
   `BHWPermutation/SourceComplexTakagiGlobal.lean`: it identifies
   `BHW.takagiHermitianEigenspace m S lambda` with Mathlib's eigenspace of
   `(S * Sᴴ).toEuclideanLin`, proves those Hermitian-square eigenvalues are
   real and nonnegative, builds
   `BHW.takagiHermitianSquareEigenvalueFixedBasis` by using the checked fixed
   basis on positive eigenspaces and `stdOrthonormalBasis` on the zero
   eigenspace, collects these bases through
   `DirectSum.IsInternal.collectedOrthonormalBasis`, reindexes the collected
   Sigma basis to `Fin m`, proves the global column equation
   `BHW.takagiHermitianSquareFixedEigenbasis_col_eigen`, and proves rank
   support from unitary diagonalization via `Matrix.rank_mul_eq_left_of_isUnit_det`,
   `Matrix.rank_mul_eq_right_of_isUnit_det`, and `Matrix.rank_diagonal`.
   Consequently `BHW.complexSymmetric_autonneTakagi_entryL1`,
   `BHW.complexSymmetric_factorSmall_rankLE`, and
   `BHW.sourceComplexSymmetric_factorSmall_rankLE` are checked without any
   remaining `hentry` parameter.  The singular-value entry-L1 bound for any
   produced Takagi diagonalization is now checked in
   `BHWPermutation/SourceComplexTakagiEntry.lean` as
   `BHW.takagi_singularValue_le_entryL1Bound`: it multiplies the Takagi
   identity by the unitary inverses, extracts `(σ a : ℂ)` as a finite double
   sum against the `a`th unitary column, and bounds that sum entrywise by
   `BHW.matrixEntryL1Bound m S`.  The same file also checks
   `BHW.complexSymmetric_entryL1_of_autonneTakagiDiagonalization`, so once the
   unitary diagonalization and rank-support identity exist, the rectangular
   entry-controlled factor follows immediately.  The final matrix-identity
   assembly is also separated and checked in
   `BHWPermutation/SourceComplexTakagiAssembly.lean`:
   `BHW.complexSymmetric_takagi_matrix_eq_of_col_eigen` proves that any
   unitary matrix whose columns satisfy
   `S *ᵥ star u_a = (σ a : ℂ) • u_a` automatically gives
   `S = U * diagonal σ * Uᵀ`; the same file checks
   `BHW.complexSymmetric_takagi_exists_unitary_of_orthonormalBasis_col_eigen`,
   which turns an orthonormal Euclidean basis satisfying this column equation
   into the required unitary matrix.  It also checks
   `BHW.complexSymmetric_takagi_exists_unitary_of_fixedHermitianEigenbasis`,
   which proves the Autonne-Takagi unitary from an orthonormal
   Hermitian-square eigenbasis whose positive-eigenvalue vectors are fixed by
   the normalized Takagi conjugation, and
   `BHW.complexSymmetric_entryL1_of_fixedHermitianEigenbasis`, which composes
   that bridge with the checked entry-L1/rank-support endpoint.  The global
   file consumes this bridge and closes the finite-dimensional Autonne-Takagi
   small-factor blocker.  It then
   spells out the finite
   support extraction: use `Fintype.nonempty_of_card_le` to embed the nonzero
   singular-value subtype into `Fin k`, define the rectangular factor by
   filling the corresponding columns and zeroing the complement, reindex the
   range sum by `Finset.sum_embedding`/`Finset.sum_bij`, and bound entries by
   the unitary-column lemma `BHW.matrix_unitary_entry_norm_le_one`, the
   Frobenius-to-entry-sum singular-value estimate
   `BHW.takagi_singularValue_le_entryL1Bound`, decomposed through
   `BHW.takagi_frobenius_sum_sq` and `BHW.real_sqrt_sum_sq_le_sum`, and the
   finite sum helper `BHW.matrixEntryL1Bound_lt_of_entry_bound` to make the
   factor entries small,
   `BHW.standardCoordinateTailSubspace`,
   `BHW.complexMinkowskiOrthogonalTailSubspace`, and
   `BHW.mem_complexMinkowskiOrthogonalTailSubspace_iff`, plus
   `BHW.complexMinkowski_realizeSmallSymmetricRankLE_inOrthogonalTail` for
   realizing the Schur residual in the orthogonal complement of the selected
   normalized block, with the arithmetic and coordinate-control helpers
   `BHW.exists_finTailEmbedding`,
   `BHW.tailEmbeddedFactorVectors`,
   `BHW.standardComplexSymmetricBilinear_tailEmbeddedFactor`,
   `BHW.tailEmbeddedFactorVectors_coord_bound`, and
   `BHW.complexMinkowskiToDotLinearEquiv_symm_coord_bound`.  The tail
   embedding is now explicit (`ι a = ⟨r + a.val, by omega⟩`), and the
   embedded-factor pairing proof is specified as a range/complement split
   followed by reindexing over `Fin k`.
   `BHW.complexMinkowski_realizeSmallSymmetricRankLE` is only the `r = 0`
   corollary of that tail theorem.  The normalized Schur proof must use the
   tail theorem, not the full-space corollary, or the residual vectors could
   disturb the selected block.  The canonical normal-form data are
   `BHW.hwLemma3CanonicalSource`,
   `BHW.hwLemma3CanonicalGram`, and
   `BHW.sourceMinkowskiGram_hwLemma3CanonicalSource`; these canonical
   statements carry both `r <= n` and `r <= d + 1`, because the first `r`
   source indices and the orthogonal tail split are not meaningful without
   the source-arity bound.  The normalized Schur step is now pinned through
   `BHW.hwLemma3_normalizedSchurBlockRealization`: decompose a nearby
   canonical Gram matrix as `[[A, Bᵀ], [B, C]]` using
   `Fin n ≃ Fin r ⊕ Fin (n-r)`, take the selected square root
   `P * Pᵀ = A`, set the selected cross coefficients
   `L := B * A⁻¹`, realize the Schur complement
   `C - B * A⁻¹ * Bᵀ` in the orthogonal tail, and assemble the perturbation
   from the selected vectors plus tail residual vectors.  This removes the
   last informal "Schur realization" step from Lemma 3.  The normal-form
   transport must be an explicit finite-dimensional packet,
   `BHW.HWLemma3NormalFormTransport` with producer
   `BHW.hwLemma3_normalFormTransportData`; this now takes the adaptedness
   hypothesis
   `Module.finrank ℂ (LinearMap.range (BHW.sourceCoefficientEval d n ζ0)) =
   BHW.sourceGramMatrixRank n (BHW.sourceMinkowskiGram d n ζ0)` and records
   the source-index linear change, ambient Minkowski isometry, Gram
   congruence, variety preservation, the oriented Gram-plus-determinant
   transport induced by Cauchy-Binet, and the two smallness estimates used to
   pull the normalized realization back to the adapted base tuple.  The
   determinant-coordinate transport is now pinned to the checked
   function-indexed model
   `BHW.sourceFullFrameDetSourceMatrixTransform`, using
   `BHW.sourceFullFrameDetFunctionCoord` to set non-injective source-label
   functions to zero.  This avoids the false overcount that would come from
   summing directly over all ordered embeddings of the same source frame; the
   identity action is checked as
   `BHW.sourceFullFrameDetSourceMatrixTransform_one` and
   `BHW.sourceOrientedGramDataSourceMatrixTransform_one`.  The actual
   row-multilinearity/Cauchy-Binet theorem is now checked as
   `BHW.sourceFullFrameDet_sourceTupleLinearChange`, with the non-injective
   terms killed by `Matrix.detRowAlternating`; the oriented invariant
   transport-on-actual-tuples theorem
   `BHW.sourceOrientedMinkowskiInvariant_sourceTupleLinearChange` and the
   variety-subtype source-matrix equivalence
   `BHW.sourceOrientedGramVarietySourceMatrixEquivOfMatrix` are also checked.
   The topological and predicate-preserving package is checked as
   `BHW.sourceOrientedGramVarietySourceMatrixHomeomorphOfMatrix`,
   `BHW.sourceOrientedGramDataSourceMatrixTransform_maxRank_iff`, and
   `BHW.sourceOrientedVarietySourceMatrixTransportEquivOfMatrix`, using the
   generic variety-relative interface
   `BHW.SourceOrientedVarietyTransportEquiv`.
   Importantly, the function-indexed determinant transform is not claimed to
   be a linear equivalence on the full independent ordered-frame coordinate
   space: it is correct on the alternating determinant coordinates realized by
   source tuples.  The chosen route is therefore the checked
   variety-relative transport interface, not a full ambient
   `SourceOrientedInvariantTransportEquiv` for source changes.  Downstream
   local-image consumers must be moved to relative-open and connectedness
   statements on the oriented variety subtype.  Its
   finite matrix assembly is not allowed to skip the intermediate
   `[[A,0],[0,0]]` stage: the projection source change
   `BHW.hwLemma3_projectionSourceChangeMatrix` sends
   `[[A,Bᵀ],[B,C]]` to `[[A,0],[0,0]]` only after
   `BHW.hwLemma3_schurComplement_eq_zero_of_rank_eq` proves
   `C - B*A⁻¹*Bᵀ = 0`; the canonical head-metric block is produced only after
   `BHW.complexSymmetric_invertible_congruence_to_sourceHeadMetric` supplies
   `P` with `P*A*Pᵀ = sourceHeadMetric d r hrD` and the head extension
   `BHW.hwLemma3_extendHeadMatrix` is composed with the projection and
   permutation matrices.  The exact support API is
   `BHW.sourceHeadHeadBlock`, `BHW.sourceTailHeadBlock`,
   `BHW.sourceTailTailBlock`,
   `BHW.sourceBlockMatrix_of_headTailBlocks` (with the source-symmetry
   hypothesis; the head/tail reconstruction from only `A`, `B`, and `C` is
   false for nonsymmetric matrices),
   `BHW.sourceGramCongruence_eq_matrix_mul`,
   `BHW.sourceGramCongruence_mul`,
   `BHW.sourceGramCongruenceLinearEquivOfMatrix`,
   `BHW.complexLorentzActionLinearEquiv`,
   `BHW.sourceFullFrameDetFunctionCoord`,
   `BHW.sourceFullFrameDetSourceMatrixTransform`,
   `BHW.sourceFullFrameDetSourceMatrixTransformLinearMap`,
   `BHW.sourceOrientedGramDataSourceMatrixTransform`,
   `BHW.sourceFullFrameDetFunctionCoord_sourceFullFrameDet`,
   `BHW.sourceFullFrameDet_sourceTupleLinearChange`,
   `BHW.sourceOrientedMinkowskiInvariant_sourceTupleLinearChange`,
   `BHW.sourceOrientedGramDataSourceMatrixTransform_mem_variety`,
   `BHW.sourceOrientedGramVarietySourceMatrixEquivOfMatrix`,
   `BHW.sourceOrientedGramVarietySourceMatrixHomeomorphOfMatrix`,
   `BHW.sourceOrientedGramDataSourceMatrixTransform_maxRank_iff`,
   `BHW.sourceOrientedVarietySourceMatrixTransportEquivOfMatrix`,
   `BHW.sourceOrientedVarietyUnderlyingSet_relOpen_of_isOpen`,
   `BHW.SourceOrientedVarietyTransportEquiv.isOpen_invFun_image`,
   `BHW.sourceOrientedVarietyTransport_invFun_image_underlying_relOpen`,
   `BHW.sourceOrientedVarietyTransport_invFun_image_eq`,
   `BHW.sourceOrientedVarietyTransport_closure_maxRankDense`,
   `BHW.sourceLinearBlockMatrix`,
   `BHW.sourceTupleLinearEquivOfMatrix`,
   `BHW.hwLemma3_projectionSourceChangeMatrix_congruence`,
   `BHW.hwLemma3_extendHeadMatrix_congruence`,
   `BHW.sourcePermutationMatrix`,
   `BHW.sourceGramMatrixRank_sourcePermuteComplexGram`,
   `BHW.sourcePermuteComplexGram_mem_sourceSymmetricMatrixSpace`,
   `BHW.hwLemma3_normalFormSourceChangeMatrix`,
   `BHW.hwLemma3_normalFormSourceChangeMatrix_det_isUnit`,
   `BHW.hwLemma3_normalFormSourceChangeMatrix_canonicalGram`,
   `BHW.complexMinkowskiNondegenerate_of_restrictedRank_eq_finrank`,
   `BHW.complexMinkowskiNondegenerate_eval_range_of_adapted`, and
   `BHW.hwLemma3_canonicalGram_tail_zero_of_adapted`.  The source-change
   adaptedness bridge is also checked:
   `BHW.sourceCoefficientEval_sourceTupleLinearChange`,
   `BHW.sourceCoefficientEval_range_sourceTupleLinearChange_eq`,
   `BHW.sourceGramMatrixRank_sourceGramCongruence`,
   `BHW.sourceTupleLinearChange_adapted_of_isUnit`,
   `BHW.sourceTupleLinearChange_tail_zero_of_canonicalGram_adapted`, and
   `BHW.hwLemma3_normalFormSourceChange_tail_zero_of_adapted`.  The checked
   canonical-tail theorem is load-bearing: it converts the adaptedness
   equality between source-span dimension and scalar rank into actual
   vanishing of tail vectors once the normalized Gram is canonical; without
   adaptedness the statement is false.  The normal-form source-change wrapper
   then applies the checked preservation of coefficient-span dimension and
   scalar Gram rank under invertible source matrices.  The selected-head
   Witt/Lorentz step is also now checked in the same file:
   `BHW.hwLemma3_canonicalGram_exists_complexLorentz_to_canonicalSource_of_adapted`
   applies the existing determinant-one complex Witt theorem
   `BHW.complexMinkowski_detOneWittExtension_to_canonicalHeadFrame` to the
   canonical head frame and uses the adapted tail-zero theorem on the tail;
   `BHW.hwLemma3_normalFormSourceChange_exists_complexLorentz_to_canonicalSource_of_adapted`
   composes this with the checked normal-form source-change matrix.  Thus the
   normalized adapted tuple is proved, not merely asserted, to lie in the
   complex Lorentz orbit of `BHW.hwLemma3CanonicalSource d n r`.  The
   base selected-block normalization also needs the arbitrary invertible
   symmetric congruence theorem to the inherited source-head metric,
   `BHW.complexSymmetric_invertible_congruence_to_sourceHeadMetric`.  This is
   now checked by the exact-rank dot-Gram route, not by the older
   orthogonal-basis placeholder: `A` is viewed as an exact-rank symmetric
   source matrix, `BHW.exists_fullRank_sourceComplexDotGram_of_rankExact`
   gives `A = Q*Qᵀ`, determinant nonvanishing forces `IsUnit Q.det`,
   `Q⁻¹` normalizes `A` to `1`, and the checked diagonal square-root
   `BHW.sourceHeadMetricSquareRoot` carries `1` to
   `sourceHeadMetric d r hrD`.  The exact checked support names are
   `BHW.sourceComplexDotGram_matrix_eq_mul_transpose`,
   `BHW.complexSymmetric_invertible_congruence_to_identity`,
   `BHW.sourceHeadMetricSquareRoot_det_isUnit`,
   `BHW.sourceHeadMetricSquareRoot_congruence`, and
   `BHW.complexSymmetric_invertible_congruence_to_sourceHeadMetric`.
   The
   perturbative selected block still uses
   `BHW.hwLemma3_selectedBlock_sqrt_near_identity`.  Then come the normalized
   surjectivity theorem
   `BHW.hwLemma3_normalizedSchurSurjective` and the transport theorem
   `BHW.hwLemma3_transport_from_normalForm`.  The adapted quantitative theorem
   also needs the explicit extended-tube shrink:
   `BHW.sourceGramCoordBall`, `BHW.isOpen_sourceGramCoordBall`, and
   `BHW.hwLemma3_adaptedBase_transport_smallPerturbation_extendedTube`; this
   is where the perturbation radius is made small enough that the realized
   adapted-base perturbations remain in `BHW.ExtendedTube d n`.  The final
   conversion from the quantitative `ε` theorem to an arbitrary neighborhood
   of the adapted representative is the finite-product open-ball helper
   `BHW.exists_coord_supnorm_ball_subset_of_isOpen` followed by
   `BHW.hwLemma3_smallPerturbation_to_adapted_localVectorRealization`; it is
   not a replacement for Lemma 3.  The open-ball helper is now pinned to a
   scratch-checked Lean proof using `Metric.mem_nhds_iff` and two nested
   applications of `pi_norm_lt_iff`; no custom finite norm-equivalence lemma
   is needed.  The exported relative-open theorem is the
   direct Lemma-3 scalar-neighborhood statement, not a prescribed-neighborhood
   theorem around the original representative.  On the maximal-rank locus,
   where Hall-Wightman Lemmas 5--7 need a scalar chart inside a prescribed
   vector neighborhood, the adaptedness is supplied directly by
   `BHW.hwSourceGramMaxRankAt_span_finrank_eq_sourceGramMatrixRank`, so the
   chart proof uses
   `BHW.hwLemma3_adapted_sourceGram_localVectorRealization` rather than the
   public arbitrary-representative theorem.  The
   global relative-open field is the union of those ambient neighborhoods,
   plus the elementary inclusion
   `BHW.sourceExtendedTubeGramDomain_subset_sourceComplexGramVariety`.  That
   inclusion is definitional in the current repo: destruct
   `Z ∈ sourceMinkowskiGram d n '' ExtendedTube d n` as
   `⟨z, hzET, rfl⟩`, then prove
   `sourceMinkowskiGram d n z ∈ sourceComplexGramVariety d n` by the range
   witness `⟨z, rfl⟩`; `hzET` is unused for the variety-membership proof.

   Lemma-3 readiness is componentwise.  The relative-open theorem may move
   to Lean only after the local-realization rows below have proof terms or
   checked local support:

   | Subpacket | Status | Proof obligation |
   | --- | --- | --- |
   | Definitional subset and connectedness | Mechanical with checked support. | Use the image/range definitions, `BHW.isConnected_extendedTube`, and `BHW.contDiff_sourceMinkowskiGram`. |
   | Pointwise-to-global relative-open assembly | Mechanical after local realization. | Choose explicit `sourceExtendedTubeGramDomain_relOpen_at` neighborhoods, form the subtype-indexed union, and use the subset lemma. |
   | Adapted same-Gram representative | Checked in `BHWPermutation/SourceHWAdaptedTubeRepresentative.lean`. | `hwLemma3_extendedTube_adaptedRankRepresentative` now consumes the checked residual-frame/all-coefficients extended-tube theorem, selected projection, Schur-zero residual theorem, and span-rank equality.  It explicitly handles `n = 0` and forbids source-changing an arbitrary representative to zero tail. |
   | Principal block/projection/Schur-zero algebra | Proof transcript pinned; principal-minor extraction checked locally. | The blueprint now gives the selected coefficient definition, projection Gram equality, residual orthogonality, residual-residual zero via the Schur complement, and span-finrank theorem.  These are finite algebra support targets, not final wrappers. |
   | Normal-form source transport | Source-level normal-form data with actual `toOriginal` is checked in `SourceOrientedRankDeficientTubeResidual.lean`. | `SourceOrientedRankDeficientNormalFormData.ofSourceMatrixLorentz`, `SourceOrientedRankDeficientNormalFormData.exists_ofAdaptedBase`, and `SourceOrientedRankDeficientNormalFormData.exists_ofExtendedTube` now assemble the adapted ET representative, rank-deficient same-oriented-invariant conversion, invertible source matrix, complex Lorentz normalization, continuous actual `toOriginal`, and variety-relative source transport.  What remains hard is the tube-valued residual-polydisc producer itself: compact tube shrink for `N.toOriginal (residualVector c)`, Schur image-surjectivity, and original-coordinate max-rank density.  The old ambient `SourceOrientedInvariantTransportEquiv` source-change target remains rejected for determinant coordinates. |
   | Near-identity square root | Proof transcript pinned; pure matrix analysis. | The blueprint gives the binomial-series construction of `(1 + B)^(1/2)`, convergence via a scalar power-series majorant, transpose compatibility, the square identity, and entrywise estimates from matrix norm bounds. |
   | Schur-rank/Takagi/tail factorization | Proof transcript pinned; pure finite linear algebra. | The proof is split into Mathlib Schur-complement rank factorization, Autonne-Takagi with rank support and explicit entry-L1 control, small factorization, and tail embedding with coordinate estimates. |
   | Orthogonal-tail residual realization | Proof transcript pinned; production Lean not started. | Takagi factors are transported into `complexMinkowskiOrthogonalTailSubspace`, paired to the Schur complement, kept orthogonal to the selected block, and transported back through the Minkowski orthogonal model with norm control. |
   | Normalized Schur realization and transport back | The canonical normal-form transport-to-center theorem, subtype-valued transported normal image, and invertible-head principal-Schur equality are checked; the concrete local-image producer is not yet implemented. | The normalized theorem assembles selected vectors, cross coefficients, and tail residuals, proves the oriented Gram/determinant equality by `sourceOrientedNormalParameterVector_realizes_schur`, identifies the resulting normal point with `sourceOrientedNormalParameterVarietyPoint`, rewrites its ordinary coordinate by `sourceOrientedNormalParameterVarietyPoint_eq_sourcePrincipalSchurGraph` on the invertible-head box, then uses `N.originalNormalVarietyPoint` to transport it back through the checked `SourceOrientedVarietyTransportEquiv` from `sourceOriented_lowRank_exists_normalFormVarietyTransport_from_canonical`. |
   | Extended-tube shrink and arbitrary-neighborhood conversion | Proof transcript pinned; topology helper standard. | `exists_coord_supnorm_ball_subset_of_isOpen` is used with openness of `ExtendedTube`; `hwLemma3_adaptedBase_transport_smallPerturbation_extendedTube` combines the shrink with the transported realization. |
   | Existing Schur/local-connectedness files | Checked support only. | `sourceComplexGramVariety_local_connectedRelOpen_basis*` and `sourcePrincipalSchurGraph_rankLE_image_eq_openCoordinatePatch` do not prove relative openness of the extended-tube Gram image. |

   Therefore, after the theorem-2 proof-doc gate is fully closed, the first
   Lean target in this block would be a finite-dimensional support theorem,
   not the wrapper `BHW.sourceExtendedTubeGramDomain_relOpen_connected`.
   This is a future implementation-order note, not permission to start
   production Lean while the oriented scalar-source producer ledger remains open.
3. `BHW.sourceVarietyGermHolomorphicOn_extendF_descent`: descend
   `BHW.extendF F` through `BHW.sourceMinkowskiGram d n` to a
   `BHW.SourceVarietyGermHolomorphicOn` scalar representative.  The branch law
   gives well-definedness, and the local Hall-Wightman source charts give
   analytic-space variety holomorphicity.  The production API must migrate the
   `SourceScalarRepresentativeData.Phi_holomorphic` field from the old strong
   `BHW.SourceVarietyHolomorphicOn` predicate to
   `BHW.SourceVarietyGermHolomorphicOn`: Hall-Wightman supplies local ambient
   representatives agreeing with the scalar function on
   `U0 ∩ BHW.sourceComplexGramVariety d n`, not one global ambient function
   holomorphic off the variety.  A preimage-choice function on
   `sourceExtendedTubeGramDomain` is still not enough; the chosen scalar value
   function must be represented locally by the Hall-Wightman scalar charts on
   the analytic variety.  The theorem-2 blueprint now names this content as
   the germ-API data `BHW.SourceVarietyGermHolomorphicOn`, the support lemmas
   `continuousOn`, `of_subset_relOpen`, `sub`,
   `precomp_sourcePermuteComplexGram`, `comp_sourceMinkowskiGram`,
   `comp_differentiableOn_chart`, and
   `sourceComplexGramVariety_identity_principle`.
   The `comp_sourceMinkowskiGram` proof must be phrased pointwise with
   `DifferentiableWithinAt.congr_of_eventuallyEq_of_mem`: after choosing the
   local ambient representative `Ψ` on an open `U0`, pull `U0` back along the
   continuous Gram map to get an event in `𝓝[Ω] z`, prove equality there by
   the germ field on `U0 ∩ sourceComplexGramVariety d n` using the witness
   `⟨w, rfl⟩`, compose the differentiability of `Ψ` with the polynomial Gram
   map, and transfer differentiability to `Phi ∘ sourceMinkowskiGram` by the
   exact Mathlib congruence theorem.  The docs must not use the old schematic
   `DifferentiableOn.congr` proof on a smaller source-shrink as if it proved
   differentiability on all of `Ω`.
   If an atlas is useful during implementation, `BHW.HallWightmanScalarGermAtlas`,
   `BHW.hallWightman_consistentScalarGermAtlas`, and
   `BHW.hallWightman_scalarGermAtlas_glue` are proof-local organization only:
   they must be private or inlined into
   `BHW.sourceVarietyGermHolomorphicOn_extendF_descent`, not exported as an
   additional source theorem surface.
   The direct descent core is split further into
   `BHW.hallWightman_localScalarChart_at`, with the separate local-chart
   predicates `BHW.HWSourceGramMaxRank` and
   `BHW.HWSourceGramExceptionalRank` and sublemmas
   `BHW.hallWightman_maxRank_localScalarChart_at` and
   `BHW.hallWightman_exceptionalRank_localScalarChart_at`.  This keeps the
   non-exceptional scalar-product chart, exceptional-rank removable-singularity
   step, and chart-overlap gluing explicit.  The theorem-2 blueprint now
   further expands those local-chart lemmas into
	   `BHW.hallWightman_maxRank_powerSeriesChart_at`,
	   `BHW.hallWightman_lorentzInfinitesimalEquations`,
	   with the Lemma-4 exp-curve support
	   `BHW.complexMinkowskiSkewGenerator_isInLieAlgebra`,
	   `BHW.ComplexMinkowskiSkewGenerator.expCurve`,
	   `BHW.complexMinkowskiSkewGenerator_expCurve_val`,
	   `BHW.complexMinkowskiSkewGenerator_expCurve_zero`,
	   `BHW.complexLorentzAction_expCurve_mem_extendedTube`,
	   `BHW.complexLorentz_expCurve_action_hasDerivAt`,
	   `BHW.differentiableAt_extendF_of_mem_extendedTube`, and
	   `BHW.extendF_expCurve_invariant`,
	   `BHW.hallWightman_maxRank_scalarDifferentials_span_PDE`,
	   with the Lemmas-6--7 tangent/dual packet
	   `BHW.sourceGramDifferential`,
	   `BHW.sourceGramDifferential_apply`,
	   `BHW.sourceGramCoordinateDifferential_apply`,
	   `BHW.sourceGramDifferential_lorentzInfinitesimalTangent_zero`,
	   `BHW.complexMinkowski_infinitesimalWittExtension`,
	   `BHW.HWMaxRankSelectedRowsData`,
	   `BHW.hwMaxRank_selectedRowsData`,
	   `BHW.hwMaxRank_kernel_row_relation_transfer`,
	   `BHW.sourceGramDifferential_kernel_eq_lorentzInfinitesimalTangent`,
	   `BHW.continuousLinearFunctional_factor_through_of_vanishes_on_ker`, and
	   `BHW.sourceGramDifferential_dual_coordinate_expansion`,
	   `BHW.HWPowerSeriesCoordinateSplit`,
   `BHW.SelectedScalarCoordinatesBasis`,
   `BHW.HWVectorCoordinateSplitData`,
   `BHW.hallWightman_independentScalarCoordinates`,
   `BHW.hallWightman_sourceVectorCoordinateSplit`,
   `BHW.exists_open_selectedMinor_ne_zero_neighborhood`,
   `BHW.sourceGramDifferential_image_basis_of_selected_minor`,
   `BHW.hallWightman_maxRank_selectedScalarDifferentials_local`,
   `BHW.hallWightman_coordinateSplit_inverseFunction`,
   `BHW.exists_sourceCoord_product_with_connected_aux_subset_open`,
   `BHW.auxiliaryCoordinateTangent`,
   `BHW.auxiliaryCoordinateTangent_selectedScalarDeriv_zero`,
   `BHW.hallWightman_auxiliaryTangent_sourceGramDifferentials_zero`,
   `BHW.fderiv_coord_pullback_extendF`,
   `BHW.hallWightman_powerSeries_coordinateSplit`,
   `BHW.hallWightman_coord_pullback_extendF`,
   `BHW.hallWightman_auxiliaryDerivative_zero`,
   `BHW.eqOn_of_fderiv_eq_zero_of_isConnected_open`,
   `BHW.holomorphic_product_independent_of_auxiliary`,
   `BHW.hallWightman_selectedScalarFunction_to_fullGramChart`,
   `BHW.hallWightman_powerSeries_from_PDE_span`,
   `BHW.hallWightman_powerSeriesChart_branch_eq_of_sameGram`,
   `BHW.hallWightman_scalarGerm_continuous_locallyBounded`,
   `BHW.continuousOn_of_open_nhdsWithin_control`,
   `BHW.continuousOn_openDomain_preimage_nhds`,
   `BHW.hwSourceGramExceptionalRank_isAnalyticSubvariety`,
   `BHW.sourceGramVariety_removableAlongExceptionalRank`, and
   `BHW.hallWightman_removableScalarChart_at`, and
   `BHW.hallWightman_localScalarChart_eq_scalarValue`, so the power-series,
   boundedness/continuity, analytic exceptional-locus, and removability inputs
   are no longer hidden in prose.  The removable theorem is now pinned as a
   consumer of `BHW.sourceGramVariety_normal_riemannExtension`: apply the
   normal analytic-space Riemann theorem to the max-rank chart section using
   `BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_maxRank` for
   the dense complement hypothesis.  The Riemann theorem is
   finite-dimensional-polymorphic, though this ordinary specialization uses
   the scalar Gram coordinate ambient type.  It internally uses the
   relative-open witness for `U` and returns the domain-control field
   `U0 ∩ BHW.sourceComplexGramVariety d n ⊆ U`.  Chart constructors must
   still preserve
   their branch-provenance fields until the descent theorem builds the
   `SourceVarietyGermHolomorphicOn` local representatives.
   The chart overlap compatibility is discharged by
   `BHW.hallWightman_localScalarChart_overlap_eq`: a scalar point in the
   overlap of two chart slices is first realized as an ordinary extended-tube
   Gram point using either chart's `U0_sub` field, and then both chart values
   are rewritten to the same `extendF F w` by their `branch_eq` fields.  No
   equality of arbitrary ambient representatives off the source Gram variety
   is used.  This helper has also been scratch-checked: from
   `G ∈ (U ∩ V) ∩ sourceComplexGramVariety d n`, form
   `hG_Uvar := ⟨hG.1.1, hG.2⟩`, use `hU_sub hG_Uvar` to get
   `G ∈ sourceExtendedTubeGramDomain d n`, destruct as `⟨w, hw, rfl⟩`,
   then close with
   `(hΨ_branch w hw hG.1.1).trans (hΧ_branch w hw hG.1.2).symm`.
   The descent theorem itself uses
   `BHW.hallWightman_localScalarChart_eq_scalarValue` to convert each local
   branch chart into a `SourceVarietyGermHolomorphicOn` representative for the
   single branch-defined scalar value `Phi`; the exceptional removable chart
   consumes the same `Phi`, together with its continuity and local boundedness,
   so there is no second hidden choice of scalar values.  The helper has now
   been scratch-checked exactly against `SourceExtension.lean`: for
   `Z ∈ U0 ∩ sourceComplexGramVariety d n`, use `hU0_sub` to get
   `Z ∈ sourceExtendedTubeGramDomain d n`, destruct it as
   `⟨w, hw, rfl⟩`, and close with
   `(hPhi_branch w hw).trans (hΨ_branch w hw hZ.1).symm`.
   The continuity/local-boundedness theorem is deliberately upstream of the
   exceptional chart theorem: it defines the scalar value by an
   extended-tube realization and uses Lemma 3 to realize nearby scalar-variety
   points inside any prescribed extended-tube neighborhood, then applies
   continuity of `extendF` on the ordinary extended tube.  It must not call
   `hallWightman_localScalarChart_at`, which would make the removability
   argument circular.  The two topology helpers in this proof are now pinned
   to direct `continuousOn_iff` proofs.  In particular,
   `BHW.continuousOn_openDomain_preimage_nhds` takes only
   `hf : ContinuousOn f Ω`, `hxΩ`, and the open target neighborhood; it does
   not carry an unused `IsOpen Ω` hypothesis.  The open extended-tube theorem
   is still used later when forming `Vsrc ∩ BHW.ExtendedTube d n`, not in this
   helper.  The first branch-defined value step is now scratch-checked on the
   honest subtype domain:
   `BHW.sourceScalarValueOfExtendFOn d n F
   (Z : {Z // Z ∈ sourceExtendedTubeGramDomain d n}) :=
   extendF F (Classical.choose Z.2)`; for
   `Z = sourceMinkowskiGram d n w`, use the subtype proof
   `⟨w, hw, rfl⟩`, the two fields of `Classical.choose_spec`, and
   `hBranch hchoose_mem hw hchoose_gram` to prove
   `BHW.sourceScalarValueOfExtendFOn_branch_eq`.  Any total ambient `phi`
   with an `else` branch is only proof-local packaging for total-function
   APIs and must not be exported as the production scalar representative.
   This helper is only the branch-defined value well-definedness calculation;
   it consumes the branch law and does not replace it.
   The max-rank chart helper
   `BHW.hallWightman_powerSeriesChart_branch_eq_of_sameGram` must carry the
   source-vector inclusion `Uvec ⊆ BHW.ExtendedTube d n`; the branch law cannot
   be applied to the Lemma-3 realization without that hypothesis.  In the
   Lemma-5 power-series proof, the selected-coordinate reinflation theorem
   `BHW.hallWightman_selectedScalarFunction_to_fullGramChart` must consume the
   local selected-coordinate differentiability on the actual product factor
   `Us` returned by `BHW.holomorphic_product_independent_of_auxiliary`; it must
   not silently strengthen this to differentiability on a global
   selected-coordinate image of the source Gram variety.  The product theorem
   must require `C.Ucoord = Us × Ua` with `Ua` connected and nonempty: zero
   derivative in auxiliary directions only proves independence on each
   connected auxiliary component, so the theorem is false without this field.
   The proof defines `Ψs u := g (u, vbase)` for some `vbase ∈ Ua`, proves
   differentiability on `Us`, and uses connectedness of `Ua` to identify
   `g (u,v)` with that base value for every `(u,v) ∈ Us × Ua`.  This
   constancy step is the exact Mathlib theorem
   `IsOpen.is_const_of_fderiv_eq_zero` from
   `Mathlib.Analysis.Calculus.MeanValue`, applied to the fixed-`u`
   auxiliary slice and `hUa_conn.isPreconnected`; before applying it, the
   proof must identify the slice derivative with the auxiliary derivative by
   the chain rule for `v ↦ (u, v)` and `ContinuousLinearMap.inr`.  The
   scratch-checked Lean proof needs the ordinary complex-analysis import
   `Mathlib.Analysis.Complex.Basic` in addition to `MeanValue`/`FDeriv.Comp`
   when isolated, and the two differentiable slices are
   `differentiable_id.prodMk (differentiable_const vbase)` and
   `((differentiable_const u).prodMk differentiable_id)`.  The bare
   `differentiable_const` and method-style
   `differentiable_const.prodMk` forms do not elaborate.  The product
   chart itself must be obtained by shrinking the inverse-function-theorem
   coordinate target: `isOpen_prod_iff` gives a product neighborhood inside
   the target, then the auxiliary factor is shrunk to a finite-dimensional
   ball using `Metric.mem_nhds_iff`, `Metric.isOpen_ball`, and
   `isConnected_ball`.  The final coordinate split must restrict the
   local homeomorphism to this product so that
   `C.Ucoord = Set.prod Us Ua` holds by definition; a mere inclusion
   `Us × Ua ⊆ C.Ucoord` is not enough for the auxiliary-independence theorem.
   The full
   scalar chart is obtained by shrinking `C.U0` to
   `C.U0 ∩ {Z | C.scalarCoord Z ∈ Us}` after writing
   `C.Ucoord = Us × Ua`; the selected-coordinate differentiability input is
   exactly on `Us`, not on the larger projection set
   `{u | ∃ v, (u,v) ∈ C.Ucoord}`.  When extracting the base scalar coordinate
   from `p0 ∈ C.Ucoord`, the Lean proof must first create
   `hp0_prod : p0 ∈ Set.prod Us Ua` by rewriting with `hprod`; only
   `hp0_prod.1` has type `p0.1 ∈ Us`.  Projecting `hp0.1` directly is invalid
   before the rewrite.  The theorem
   `BHW.hallWightman_powerSeries_from_PDE_span` carries the maximal scalar-rank
   hypothesis `HWSourceGramMaxRankAt d n z0`; this is not redundant with the
   PDE-span hypothesis, because constant-rank shrinking is what makes the
   selected scalar coordinates control the full source-Gram differential image
   throughout the product chart.
   The same Lemma-5 packet must carry the full local differentiable chart
   data, not just a topological coordinate equivalence: `coordMap` and
   `coordSymmMap` are differentiable on the selected opens and inverse there.
   The coordinate pullback theorem
   `BHW.hallWightman_coord_pullback_extendF` is now pinned to the concrete
   proof `g p := extendF F (C.coordSymmMap p)`,
   `hF_holo_ext.comp C.coordSymmMap_diff`, and the maps-to proof
   `p ∈ C.Ucoord ↦ C.Uvec_sub_extendedTube (C.coordSymmMap_mem p hp)`.
   The branch equality is not a subtype-homeomorphism handwave: rewrite
   `(C.coord z).1` by `← C.coordMap_eq_coord z`, then apply
   `C.coordSymmMap_coordMap z.1 z.2`.  This pattern has been scratch-checked
   in a simplified `HWPowerSeriesCoordinateSplit` structure.
   The derivative version `BHW.fderiv_coord_pullback_extendF` must also take
   `hF_holo_ext`; branch equality alone only gives
   `g =ᶠ[𝓝 p] (fun q => extendF F (C.coordSymmMap q))` by
   `Filter.EventuallyEq.fderiv_eq`.  The actual derivative formula then uses
   `fderiv_comp'` with `hF_holo_ext.differentiableAt` on the open ordinary
   extended tube and `C.coordSymmMap_diff.differentiableAt` on `C.Ucoord`.
   Scratch Lean checked this proof pattern with
   `Mathlib.Analysis.Calculus.FDeriv.Congr`.
   It must also carry local, not merely basepoint, scalar differential data:
   `BHW.HWPowerSeriesCoordinateSplit.sourceGramDifferentials_selected_local`
   says selected scalar differentials span the full source-Gram differential
   image at each chart point, while `BHW.HWPowerSeriesCoordinateSplit.span_local`
   is filled after shrinking to the constant-rank non-exceptional chart.  The
   named source of both fields is
   `BHW.hallWightman_maxRank_selectedScalarDifferentials_local`.  The
   finite-dimensional basis packet must include
   `SelectedScalarCoordinatesBasis.card_eq_expected : e =
   BHW.sourceGramExpectedDim d n`; independence of the selected differentials
   on the shrunken chart is not enough to prove that all source-Gram
   coordinate differentials lie in their span without this dimension equality.
   `BHW.hallWightman_auxiliaryDerivative_zero` first differentiates
   `coordMap (coordSymmMap p) = p` to kill selected scalar derivatives on
   auxiliary tangents, then uses the selected-span field to kill all source
   Gram differentials, and finally derives Lemma-4 PDE pointwise from
   `BHW.hallWightman_lorentzInfinitesimalEquations`.  The selected-derivative
   sublemma now uses `Filter.EventuallyEq.fderiv_eq` directly; it does not
   pass differentiability arguments to that theorem.  The zero derivative of
   `q ↦ q.1 b` on an auxiliary vector is written explicitly as the continuous
   linear map
   `(ContinuousLinearMap.proj b).comp (ContinuousLinearMap.fst ℂ _ _)`,
   whose `fderiv` is itself, so evaluation at `(0,v)` is definitionally zero.
   The differentiability of the selected coordinate projection itself should
   use `(ContinuousLinearMap.proj b).hasFDerivAt.differentiableAt`; this is the
   checked `ContinuousLinearMap.hasFDerivAt` API exported by the usual
   FDeriv affine/linear imports.
   The chain step is `fderiv_comp'` for
   `(fun y => C.scalarCoord (sourceMinkowskiGram d n y) b) ∘
   C.coordSymmMap`.  Lemma 4 itself is now
   implementation-level: convert the skew matrix to
   `ComplexLorentzGroup.IsInLieAlgebra`, define
   `expCurve A t = ComplexLorentzGroup.expLieAlg (t • A.val)`, prove the
   generated action has derivative
   `lorentzInfinitesimalTangent d n A z0` at `0`, compose with the
   differentiability of `extendF F` on the open ordinary extended tube, and
   identify the derivative with zero because
   `BHW.extendF_complexLorentzInvariant_of_cinv` makes
   `extendF F (expCurve A t · z0)` constant in `t`.  This step may not be
   replaced by an ambient invariant-function theorem.  Lemmas 6--7 are also
   expanded to implementation level: prove that the kernel of the source Gram
   differential at a max-rank point is exactly the range of infinitesimal
   Lorentz tangents, using the infinitesimal Witt-extension theorem, then
   factor every covector annihilating those tangents through the source Gram
   differential and expand the resulting finite-product dual functional in
   coordinate scalar-product differentials.  The annihilator factor theorem
   `BHW.continuousLinearFunctional_factor_through_of_vanishes_on_ker` is now
   pinned to a scratch-checked Lean proof: lift `ℓ.toLinearMap` through
   `Submodule.liftQ` on `LinearMap.ker L.toLinearMap`, identify the quotient
   with `LinearMap.range L.toLinearMap` by `LinearMap.quotKerEquivRange`,
   extend the resulting range functional to the ambient codomain with
   `LinearMap.exists_extend`, and turn the extension into a continuous linear
   map with `LinearMap.continuous_of_finiteDimensional`.  The finite dual
   expansion theorem `BHW.sourceGramDifferential_dual_coordinate_expansion`
   is also pinned to a scratch-checked Lean proof: expand
   `ψ : (Fin n -> Fin n -> ℂ) ->L[ℂ] ℂ` in the finite coordinate basis
   `Pi.single i (Pi.single j 1)`, compose the equality with
   `sourceGramDifferential d n z0`, and identify each composed coordinate
   probe with `sourceGramCoordinateDifferential d n z0 i j` using
   `BHW.sourceGramCoordinateDifferential_apply`.
   The kernel theorem
   `BHW.sourceGramDifferential_kernel_eq_lorentzInfinitesimalTangent` is now
   pinned to a full finite-dimensional proof transcript as well.  The forward
   implication first chooses `BHW.hwMaxRank_selectedRowsData`, extracts the
   selected-row compatibility equations from `hDq :
   sourceGramDifferential d n z0 X = 0`, and invokes
   `BHW.complexMinkowski_infinitesimalWittExtension` to get a skew generator
   matching the selected velocity rows.  If `d + 1 <= n`, the selected rows
   span the whole ambient space; for an arbitrary row `r`, write `z0 r` as a
   finite linear combination of selected rows and use
   `BHW.hwMaxRank_kernel_row_relation_transfer` to prove the same relation for
   `X r`, after which linearity of `lorentzInfinitesimalTangent` in `z0`
   closes the row.  If `n <= d + 1`, `S.I` is surjective and every row is
   already selected.  The reverse implication is the direct expansion
   `BHW.sourceGramDifferential_lorentzInfinitesimalTangent_zero`, where the
   double sum cancels coefficientwise by the Minkowski-skew relation.  This is
   the exact Lemmas 6--7 rank computation, not an analytic-continuation step.
   Max-rank chart readiness is therefore a componentwise proof obligation,
   not a name-introduction task.  Production Lean for
   `BHW.hallWightman_powerSeries_from_PDE_span` may start only after the
   following subproofs have complete source-level transcripts:
   `BHW.hallWightman_lorentzInfinitesimalEquations` from the explicit
   complex-Lorentz `expCurve`;
   `BHW.sourceGramDifferential_kernel_eq_lorentzInfinitesimalTangent` from
   infinitesimal Witt extension;
   `BHW.continuousLinearFunctional_factor_through_of_vanishes_on_ker` and
   `BHW.sourceGramDifferential_dual_coordinate_expansion` for the dual
   expansion;
   `BHW.hallWightman_coordinateSplit_inverseFunction` with differentiable
   `coordMap`/`coordSymmMap`, product equality
   `C.Ucoord = Set.prod Us Ua`, and connected nonempty auxiliary factor;
   `BHW.hallWightman_auxiliaryDerivative_zero` using the local selected-span
   fields at every chart point;
   `BHW.holomorphic_product_independent_of_auxiliary` using
   `IsOpen.is_const_of_fderiv_eq_zero` on the fixed auxiliary slice; and
   `BHW.hallWightman_selectedScalarFunction_to_fullGramChart` with source
   variety domain control.  The assembly theorem
   `BHW.hallWightman_maxRank_powerSeriesChart_at` may then add Lemma 3's
   local realization and
   `BHW.hallWightman_powerSeriesChart_branch_eq_of_sameGram`; it must not be
   used to smuggle any of those pieces as assumptions.
   In the
   Lean-shaped proof, destruct
   `hZU : Z ∈ sourceExtendedTubeGramDomain d n` as
   `⟨z0, hz0, rfl⟩`, and when applying the helper to a realized
   extended-tube point `w`, add the variety membership
   `⟨w, rfl⟩` to upgrade `sourceMinkowskiGram d n w ∈ U0 ∩ O` to
   membership in `(U0 ∩ O) ∩ sourceComplexGramVariety d n`.
   Descent/max-rank/removable readiness is likewise componentwise.  The
   descent theorem may move to Lean only after these local-chart and
   removability rows have proof terms or checked local support:

   | Subpacket | Status | Proof obligation |
   | --- | --- | --- |
   | Germ API and chart-to-`Phi` compatibility | Checked API plus scratch-pinned helper. | Use `SourceVarietyGermHolomorphicOn` and `hallWightman_localScalarChart_eq_scalarValue`; equality is only on the source Gram variety slice. |
   | Branch-defined scalar value, continuity, local boundedness | Proof transcript pinned; production Lean not started. | `sourceScalarValueOfExtendFOn` defines the branch value on the subtype `sourceExtendedTubeGramDomain d n`, and `sourceScalarValueOfExtendFOn_branch_eq` proves well-definedness from the branch law.  The blueprint now proves continuity/local boundedness from Lemma-3 neighborhoods directly; ambient total functions remain proof-local API packaging with irrelevant off-domain values. |
   | Lemma 4 infinitesimal PDE | Proof transcript pinned; production Lean not started. | Build the complex-Lorentz exp curve, compute its action derivative, and use differentiability plus extended-tube invariance of `extendF`. |
   | Lemmas 6--7 kernel and dual span | Proof transcript pinned; production Lean not started. | Selected rows, infinitesimal Witt extension, row-relation transfer, covector factorization through the Gram differential, and finite coordinate-dual expansion. |
   | Max-rank selected coordinates and vector split | Proof transcript pinned; production Lean not started. | Nonzero selected scalar minor at rank `min (d + 1) n`, constant-rank persistence, auxiliary coordinate complement, and finite-dimensional inverse function theorem. |
   | Product target and auxiliary independence | Product-slice transcript pinned; production Lean not started. | Restrict the IFT target to `Set.prod Us Ua`, require connected nonempty `Ua`, prove zero auxiliary derivative, and apply `IsOpen.is_const_of_fderiv_eq_zero` only on the auxiliary slice. |
   | Selected-coordinate reinflation | Lean-shaped transcript pinned; depends on coordinate split implementation. | Define the exact open `C.U0 ∩ {Z | C.scalarCoord Z ∈ Us}`, prove differentiability of `Ψs ∘ C.scalarCoord`, and keep source-variety domain control. |
   | Max-rank scalar chart assembly | Assembly transcript pinned; not a first Lean target. | Combine the product chart with Lemma 3's adapted local realization and the branch-law transport helper only after the coordinate/PDE rows are implemented. |
   | Exceptional analytic locus and dense complement | Checked for the oriented route. | `SourceOrientedAnalyticSubvariety.lean` proves the finite-equation `IsAnalyticSubvarietyIn` theorem from checked maximal-minor equations; density of the non-exceptional domain complement is already checked by the residual-chart Schur-product perturbation argument. |
   | Normal analytic-space removability | SCV support transcript pinned; production Lean not started. | Normality is reduced to the symmetric determinantal variety, Schur local product model, singular-locus codimension, the reduced Cohen-Macaulay/Jozefiak-Pragacz coordinate-ring theorem, Serre assembly, and the normal analytic-space Riemann extension with continuity/local boundedness hypotheses. |
   | `sourceVarietyGermHolomorphicOn_extendF_descent` | Mechanical only after all rows above. | Construct `SourceVarietyGermHolomorphicOn` for the same branch-defined `Phi`; do not glue in a second scalar value function. |

   Therefore, after the theorem-2 proof-doc gate is fully closed, the first
   Lean target in this descent block would be a lower support theorem, not
   `BHW.sourceVarietyGermHolomorphicOn_extendF_descent`,
   `BHW.hallWightman_localScalarChart_at`, or the final scalar-representative
   constructor.  This is a future implementation-order note, not permission to
   start production Lean while the oriented scalar-source producer ledger remains open.
4. `BHW.sourceScalarRepresentativeData_of_branchLaw`: assemble
   `BHW.SourceScalarRepresentativeData` with
   `U = BHW.sourceExtendedTubeGramDomain d n`, using the relative-open,
   connectedness, descent, and branch-equality fields.  Because the
   constructor is data-valued while the descent theorem is proposition-valued,
   the Lean assembly must extract the scalar representative by
   `let Phi := Classical.choose hDesc` and use
   `Classical.choose_spec hDesc` for `Phi_holomorphic` and `branch_eq`; a
   direct `rcases hDesc` into the structure is not accepted by Lean's
   `Prop`-elimination rules.  This is not a new assumption: it is the
   noncomputable extraction of an already proved Hall-Wightman existence
   theorem.  The exact constructor proof has now been scratch-checked with
   `SourceExtension.lean` imported: define
   `Phi := Classical.choose hDesc`, take
   `hPhi_spec := Classical.choose_spec hDesc`, and fill
   `U`, `U_eq`, `U_relOpen`, `U_connected`, `Phi`, `Phi_holomorphic`, and
   `branch_eq` directly from `sourceExtendedTubeGramDomain`, `hGeom`, and
   `hPhi_spec`.
5. `BHW.hallWightman_sourceScalarRepresentativeData` composes the preceding
   four obligations for a general forward-tube function; only then does
   `BHW.sourceScalarRepresentativeData_bvt_F` specialize it using
   `bvt_F_holomorphic` and
   `bvt_F_complexLorentzInvariant_forwardTube`, both transported across
   `BHW_forwardTube_eq` to the `BHW.ForwardTube` API used by the source
   theorem statement, plus the now-explicit
   `BHW.bvt_F_realOrthoChronousInvariant`/improper-component input needed for
   full-rank same-Gram fibres.  Since that improper-component input is not
   currently available from the local OS axioms, this specialization is
   conditional rather than Lean-ready.

Scalar-source implementation ledger:

| Surface | Current status | First missing mathematical input |
| --- | --- | --- |
| `BHW.extendedTube_same_sourceGram_extendF_eq` | Conditional pure-Gram transcript pinned; not an active Lean target on the oriented route. | Hall-Wightman Lemma-2 branch law: high-rank span isometry/Witt extension with determinant orientation/improper-component split, and low-rank isotropic contraction limit.  On the active route this is replaced by `BHW.extendedTube_same_sourceOrientedInvariant_extendF_eq`. |
| `BHW.sourceExtendedTubeGramDomain_relOpen_connected` | Conditional pure-Gram transcript pinned; connectedness mechanical. | Relative openness consumes Lemma-3 local vector realization, including singular rank.  On the active route this is replaced by `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected`. |
| `BHW.sourceVarietyGermHolomorphicOn_extendF_descent` | Conditional pure-Gram transcript pinned; not an active Lean target on the oriented route. | The germ API and mechanical glue are checked; max-rank scalar charts, continuity/local boundedness, and exceptional-rank removability supply the actual source proof.  On the active route this is replaced by `BHW.sourceOrientedVarietyGermHolomorphicOn_extendF_descent`. |
| `BHW.sourceScalarRepresentativeData_of_branchLaw` | Mechanical after descent. | No new mathematics; `Classical.choose` from a proved descent existence and `hGeom`. |
| `BHW.hallWightman_sourceScalarRepresentativeData` | Mechanical after the first three rows. | Composition of branch law, scalar-domain geometry, and descent. |
| `BHW.sourceScalarRepresentativeData_bvt_F` | Conditional only; not an active Lean target on the current strict proper-complex OS surface. | If the full-component route is sourced, specialize to `bvt_F` using `bvt_F_holomorphic`, `bvt_F_complexLorentzInvariant_forwardTube`, `BHW.bvt_F_realOrthoChronousInvariant`, and `BHW_forwardTube_eq`; otherwise replace this pure-Gram surface by the oriented scalar-source API before migrating adjacent consumers. |

The last three rows must not be implemented first as wrappers.  A future Lean
pass starts only at a row whose missing mathematical input has a complete
proof transcript or an approved source boundary.

Source-to-Lean obligation matrix for the same scalar-source gate:

| Source step | Required Lean surfaces | Current readiness |
| --- | --- | --- |
| Hall-Wightman Lemma 1 | `BHW.extendF_holomorphicOn`, `BHW.extendF_complex_lorentz_invariant`, `BHW.extendF_complexLorentzInvariant_of_cinv`, `BHW.HallWightmanFullComplexLorentzGroup`, `BHW.HallWightmanFullComplexLorentzInvariantOnForwardTube`, `BHW.fullOrthochronousRealLorentz_preserves_forwardTube`, `BHW.hallWightman_improperComponentInvariant_forwardTube`, and `BHW.hallWightmanFullComplexLorentzInvariantOnExtendedTube_eq` | Proper determinant-`1` `extendF` support now has a checked direct bridge in `ComplexInvariance/Extend.lean` via `BHW.extendF_preimage_eq_of_cinv`.  The conditional pure-Gram fork still needs the improper-component source input because proper invariance alone has a full-rank determinant obstruction; the active oriented fork avoids that input by carrying full-frame determinants. |
| Lemma 2, high rank | Checked finite support: `BHW.HWHighRankSpanIsometryData`, `BHW.hw_highRank_spanIsometryData_of_sameSourceGram`; public orbit assembly transcript pinned. | Coefficient quotient, common Gram kernel, nondegenerate restricted span, and span-isometry data are implemented in `BHWPermutation/SourceRank.lean`.  The full-complex group algebra, nondegenerate-complement Witt extension transcript, complex symmetric-form classification helper, full-frame determinant-ratio theorem, proper-span complement/nonisotropic theorem, Householder determinant subpacket, and final vectorwise-to-configuration orbit conversion now have Lean-shaped pseudo-code, with several lower pieces scratch-checked.  Production Lean must start at those finite-dimensional support lemmas, not at the public orbit theorem. |
| Lemma 2, low rank | `BHW.HWSameSourceGramSingularContractionData`, `BHW.hw_sameSourceGram_singular_contractionData`, `BHW.hw_sameSourceGram_singularLimit_extendF_eq` | Proof transcript pinned.  The residual isotropic-frame geometry, coefficient-freedom extended-tube theorem, null-boost contraction family, and two-curve continuity limit inside `ExtendedTube d n` are decomposed into named Lean surfaces. |
| Lemma 3 | `BHW.hwLemma3_extendedTube_adaptedRankRepresentative`, `BHW.hwLemma3_adapted_sourceGram_localVectorRealization`, `BHW.sourceExtendedTubeGramDomain_relOpen` | Proof transcript pinned.  Connectedness is mechanical; relative openness is reduced to adapted same-Gram realization, normal-form transport, Schur/Takagi residual realization, and the final extended-tube shrink. |
| Lemma 4 | `BHW.ComplexMinkowskiSkewGenerator`, `BHW.lorentzInfinitesimalTangent`, `BHW.hallWightman_lorentzInfinitesimalEquations` | Proof transcript pinned; production must differentiate the complex Lorentz exponential curve and use extended-tube invariance of `extendF`. |
| Lemmas 5--7 | `BHW.sourceGramDifferential_*`, `BHW.hallWightman_maxRank_scalarDifferentials_span_PDE`, `BHW.hallWightman_powerSeries_from_PDE_span`, `BHW.hallWightman_maxRank_powerSeriesChart_at` | Proof transcript pinned.  The finite-dimensional kernel/rank theorem, selected-row data, auxiliary-coordinate split, and power-series independence at rank `min (d + 1) n` are recorded; production Lean must implement those rows before max-rank scalar charts. |
| Continuity/local boundedness | `BHW.hallWightman_scalarGerm_continuous_locallyBounded` | Proof transcript pinned.  It uses Lemma 3 directly to transfer neighborhood control from `extendF`, avoids circular dependence on exceptional local charts, and supplies the weakly holomorphic input for removability. |
| Removability on the scalar variety | `BHW.hwSourceGramExceptionalRank_isAnalyticSubvariety`, `BHW.sourceComplexGramVariety_normal`, `BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_maxRank`, `BHW.sourceGramVariety_normal_riemannExtension`, `BHW.hallWightman_exceptionalRank_localScalarChart_at` | Proof transcript pinned with a standard SCV/algebraic support boundary.  The Lean port must prove or sorry-free import symmetric determinantal normality and the normal analytic-space Riemann theorem; it may not hide this behind theorem-2 wrapper surfaces. |

Therefore the first Lean implementation target after the proof-doc gate must
be one of these mathematical source rows, not
`BHW.sourceScalarRepresentativeData_bvt_F` or any downstream adjacent
`S'_n` wrapper.

Local low-level source audit, 2026-05-01, updated 2026-05-02: the production
source-complex files
do contain rank-variety and Schur-chart substrate such as
`sourceSymmetricRankLEVariety`,
`sourceComplexGramVariety_eq_sourceSymmetricRankLEVariety`, local
rank-exact identity support, and the germ pullback/identity APIs.  The
rank-split and coefficient-map substrates are now checked in
`BHWPermutation/SourceRank.lean` and
`BHWPermutation/SourceCoefficient.lean`: `BHW.sourceGramMatrixRank`,
`BHW.sourceConfigGramMatrixRank`, `BHW.HWSourceGramOrbitRank`,
`BHW.HWSourceGramLowRank`, `BHW.HWSourceGramOrbitRankAt`,
`BHW.HWSourceGramLowRankAt`, `BHW.HWSourceGramMaxRank`,
`BHW.HWSourceGramExceptionalRank`, `BHW.HWSourceGramMaxRankAt`,
`BHW.HWSourceGramExceptionalRankAt`, the rank complement/same-Gram transport
lemmas, `BHW.sourceCoefficientEval`,
`BHW.sourceCoefficientGramMap`, `BHW.sourceCoefficientGramKernel`,
`BHW.sourceCoefficientGramMap_apply_sourceMinkowskiGram`,
`BHW.sourceCoefficientEval_single`,
`BHW.sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero`,
`BHW.sourceCoefficientEval_pair_eq_sum_gram`,
`BHW.sourceCoefficientGramMap_eq_toLin_transpose`, and
`BHW.sourceCoefficientEval_ker_le_gramKernel`, plus
`BHW.restrictedMinkowskiLeftMap`, `BHW.restrictedMinkowskiRadical`,
`BHW.restrictedMinkowskiRank`, and
`BHW.sourceCoefficientEval_mem_restrictedMinkowskiRadical_iff`,
`BHW.sourceCoefficientGramKernel_eq_eval_preimage_radical`,
`BHW.sourceGramMatrixRank_eq_finrank_range_sourceCoefficientGramMap`,
`BHW.finrank_range_sourceCoefficientGramMap_eq_restrictedRank`, and
`BHW.sourceGramMatrixRank_eq_restrictedMinkowskiRank_range`, plus
`BHW.ComplexMinkowskiNondegenerateSubspace`,
`BHW.restrictedMinkowskiRadical_nontrivial_of_degenerate`,
`BHW.restrictedMinkowskiRank_lt_finrank_of_degenerate`,
`BHW.finrank_range_sourceCoefficientEval_le`,
`BHW.finrank_restrictedSpan_le_d_of_degenerate`,
`BHW.sourceGramMatrixRank_lt_orbitThreshold_of_range_degenerate`,
`BHW.hw_highRank_eval_range_nondegenerate`,
`BHW.hw_highRank_eval_ker_eq_gramKernel`, and
`BHW.hw_highRank_sourceCoefficientEval_ker_eq_of_sameSourceGram`, plus
`BHW.hwHighRankSpanIsometryOfKernelEq`,
`BHW.hwHighRankSpanIsometry_apply_eval`,
`BHW.HWHighRankSpanIsometryData`,
`BHW.hw_highRank_spanIsometryData_of_sameSourceGram`, and
`BHW.HWHighRankSpanIsometryData_sourceGram_eq`.  They do not currently contain
production declarations named
`BHW.HallWightmanFullComplexLorentzGroup`,
`BHW.HallWightmanFullComplexLorentzInvariantOnForwardTube`,
`BHW.realFullLorentzAction`,
`BHW.fullOrthochronousRealLorentz_preserves_forwardTube`,
`BHW.fullComplexLorentz_properInv_mul_full_mul_proper`,
`BHW.fullComplexLorentz_preimage_map_eq`,
`BHW.extendF_eq_preimage_value`,
`BHW.hallWightman_improperComponentInvariant_forwardTube`,
`BHW.hallWightmanFullComplexLorentzInvariantOnExtendedTube_eq`,
`BHW.bvt_F_realOrthoChronousInvariant`,
`BHW.hw_sameSourceGram_singularLimit_extendF_eq`,
`BHW.hwLemma3_extendedTube_adaptedRankRepresentative`,
`BHW.hwLemma3_adapted_sourceGram_localVectorRealization`,
`BHW.hallWightman_maxRank_powerSeriesChart_at`,
`BHW.hallWightman_scalarGerm_continuous_locallyBounded`,
`BHW.hwSourceGramExceptionalRank_isAnalyticSubvariety`,
`BHW.sourceComplexGramVariety_normal`, or
`BHW.sourceGramVariety_normal_riemannExtension`.  These are proof-doc theorem
slots, not checked local inputs.

None of these theorem-slot surfaces is currently implemented in Lean; the
current production file `BHWPermutation/SourceExtension.lean` intentionally
keeps this Hall-Wightman/BHW branch-law theorem in proof docs until the proof
or an approved source-import boundary is available.

Current readiness verdict: production Lean must still stop before
`BHW.sourceScalarRepresentativeData_bvt_F`.  The germ API and the downstream
source-variety consumers are checked production infrastructure, and the
adjacent path API has now been verified locally, but the upstream
Hall-Wightman scalar representative theorem still depends on either
implementation of the named Lemma-2, Lemma-3, Lemma-5--7, and normal
analytic-space removable packets, or an explicit user-approved source-import
boundary with exactly those theorem statements and no theorem-2/locality
content.  Adding the scalar-source theorem names to production without those
proofs would be wrapper churn, not mathematical progress.

Germ-API migration transcript before any Hall-Wightman production theorem:

1. In `BHWPermutation/SourceExtension.lean`, keep the existing
   `SourceVarietyHolomorphicOn` only as a legacy strong sufficient predicate
   and add the active predicate:

   ```lean
   def BHW.SourceVarietyGermHolomorphicOn
       (d n : ℕ)
       (Φ : (Fin n -> Fin n -> ℂ) -> ℂ)
       (U : Set (Fin n -> Fin n -> ℂ)) : Prop :=
     ∀ Z, Z ∈ U ->
       ∃ U0 Ψ,
         IsOpen U0 ∧ Z ∈ U0 ∧
         DifferentiableOn ℂ Ψ U0 ∧
         Set.EqOn Φ Ψ (U0 ∩ BHW.sourceComplexGramVariety d n) ∧
         U0 ∩ BHW.sourceComplexGramVariety d n ⊆ U
   ```

   Also add the elementary support helper
   `BHW.IsRelOpenInSourceComplexGramVariety.subset`:

   ```lean
   theorem BHW.IsRelOpenInSourceComplexGramVariety.subset
       {U : Set (Fin n -> Fin n -> ℂ)}
       (hU : BHW.IsRelOpenInSourceComplexGramVariety d n U) :
       U ⊆ BHW.sourceComplexGramVariety d n := by
     rcases hU with ⟨U0, hU0_open, hU_eq⟩
     intro Z hZU
     rw [hU_eq] at hZU
     exact hZU.2
   ```

   The support lemmas are not wrappers: they expose exactly the analytic-space
   operations needed by downstream theorem 2:
   `SourceVarietyHolomorphicOn.to_germ`,
   `SourceVarietyGermHolomorphicOn.continuousOn` with the subset hypothesis
   `U ⊆ sourceComplexGramVariety d n`,
   `SourceVarietyGermHolomorphicOn.of_subset_relOpen`,
   `SourceVarietyGermHolomorphicOn.sub`, and
   `SourceVarietyGermHolomorphicOn.precomp_sourcePermuteComplexGram`.
   In `precomp_sourcePermuteComplexGram`, the local representative is
   `Ψ ∘ sourcePermuteComplexGram n σ` on the preimage of the old chart; the
   variety-slice equality uses
   `sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff`.

2. Change the two production data/predicate fields in
   `SourceExtension.lean`, not by adding parallel public structures:

   ```lean
   structure BHW.SourceScalarRepresentativeData ... where
     ...
     Phi_holomorphic :
       BHW.SourceVarietyGermHolomorphicOn d n Phi U

   def BHW.sourceDistributionalUniquenessSetOnVariety ... : Prop :=
     E.Nonempty ∧
       ∀ U Φ Ψ,
         BHW.IsRelOpenInSourceComplexGramVariety d n U ->
         IsConnected U ->
         (∀ G ∈ E, BHW.sourceRealGramComplexify n G ∈ U) ->
         BHW.SourceVarietyGermHolomorphicOn d n Φ U ->
         BHW.SourceVarietyGermHolomorphicOn d n Ψ U ->
         (∀ G ∈ E,
           Φ (BHW.sourceRealGramComplexify n G) =
             Ψ (BHW.sourceRealGramComplexify n G)) ->
         Set.EqOn Φ Ψ U
   ```

   Transitional aliases may be private inside one commit if needed for local
   proof organization, but the public theorem-2 surface must not expose both
   a strong and a germ version.  The strong predicate can still map into the
   germ predicate by `SourceVarietyHolomorphicOn.to_germ`.

3. In `BHWPermutation/SourceComplexDensity.lean`, the germ consumers are
   ported under the production theorem names, rather than under parallel
   `_germ` wrappers.  The checked declarations have the following shapes:

   ```lean
   theorem BHW.SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram
       {U : Set (Fin n -> Fin n -> ℂ)}
       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
       {V : Set (Fin n -> Fin (d + 1) -> ℂ)}
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hGramU : BHW.sourceMinkowskiGram d n '' V ⊆ U) :
       DifferentiableOn ℂ
         (fun z => H (BHW.sourceMinkowskiGram d n z)) V

   theorem BHW.sourceComplexGramVariety_identity_principle
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hU_conn : IsConnected U)
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0 U
   ```

   The identity-principle port is not one monolithic rename.  The internal
   germ ladder is present before the public theorem is used downstream:

   ```lean
   theorem BHW.sourceComplexGramVariety_rankExact_local_identity_near_point
       (hD : d + 1 < n)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hZ0U : Z0 ∈ U)
       (hZ0reg :
         Z0 ∈ BHW.sourceSymmetricRankExactStratum n (d + 1))
       (hA_rel :
         ∃ A0, IsOpen A0 ∧
           A = A0 ∩
             (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
       (hZ0_closure : Z0 ∈ closure A)
       (hA_zero : Set.EqOn H 0 A) :
       ∃ V, Z0 ∈ V ∧
         (∃ V0, IsOpen V0 ∧
           V = V0 ∩
             (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))) ∧
         Set.EqOn H 0 V

   theorem BHW.sourceComplexGramVariety_rankExact_identity_principle_of_connected
       (hD : d + 1 < n)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hUreg_conn :
         IsConnected
           (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0
         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))

   theorem BHW.sourceComplexGramVariety_identity_principle_of_connected_rankExact
       (hD : d + 1 < n)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hUreg_conn :
         IsConnected
           (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0 U

   theorem BHW.sourceComplexGramVariety_rankExact_identity_principle
       (hD : d + 1 < n)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hU_conn : IsConnected U)
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0
         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))

   theorem BHW.sourceComplexGramVariety_identity_principle_easy
       (hn : n <= d + 1)
       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
       (hU_conn : IsConnected U)
       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
       (hW_ne : W.Nonempty)
       (hW_sub : W ⊆ U)
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hW_zero : Set.EqOn H 0 W) :
       Set.EqOn H 0 U
   ```

   `sourceComplexGramVariety_identity_principle` is then only the final
   arity split:

   ```lean
   by_cases hn : n <= d + 1
   · exact BHW.sourceComplexGramVariety_identity_principle_easy
       hn hU_rel hU_conn hW_rel hW_ne hW_sub hH hW_zero
   · have hD : d + 1 < n := by omega
     exact BHW.sourceComplexGramVariety_identity_principle_of_connected_rankExact
       hD hU_rel
       (BHW.sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
         d n hD hU_rel hU_conn)
       hW_rel hW_ne hW_sub hH hW_zero
   ```

   The final dense-extension line inside
   `sourceComplexGramVariety_identity_principle_of_connected_rankExact`
   must call

   ```lean
   BHW.sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact
     d n (Nat.le_of_lt hD) hU_rel
     (BHW.SourceVarietyGermHolomorphicOn.continuousOn d n hH
       (BHW.IsRelOpenInSourceComplexGramVariety.subset hU_rel))
     hzero_reg
   ```

   `comp_sourceMinkowskiGram` is a local representative proof: at `z ∈ V`,
   choose `U0, Ψ` for `H` at `sourceMinkowskiGram d n z`, shrink the source
   by the open preimage of `U0`, and rewrite to
   `Ψ ∘ sourceMinkowskiGram` because every Gram value lies in
   `sourceComplexGramVariety d n` by definition.  The identity principle uses
   the same rank-exact, connected-regular-locus, and density proof already
   checked before the migration; the only changes are replacing composition by
   the germ local representative and using
   `SourceVarietyGermHolomorphicOn.continuousOn
     (BHW.IsRelOpenInSourceComplexGramVariety.subset hU_rel)`
   in the dense lower-rank extension.

   `BHW.os45AdjacentScalarEq_on_quarterTurnCorridor` has been ported in the
   same file: it proves `hΨ_holo`, `hΦ_holo`, and `hH_holo` with the germ
   `of_subset_relOpen`, `precomp_sourcePermuteComplexGram`, and `sub`, and
   calls `sourceComplexGramVariety_identity_principle`.

4. In `BHWPermutation/SourceComplexLocalChart.lean`, the checked germ chart
   pullback is:

   ```lean
   theorem BHW.SourceVarietyGermHolomorphicOn.comp_differentiableOn_chart
       (d n N : ℕ)
       {D : Set (Fin N -> ℂ)}
       {Γ : (Fin N -> ℂ) -> (Fin n -> Fin n -> ℂ)}
       (hH : BHW.SourceVarietyGermHolomorphicOn d n H U)
       (hΓU : Γ '' D ⊆ U)
       (hΓvar : Γ '' D ⊆ BHW.sourceComplexGramVariety d n)
       (hΓdiff : DifferentiableOn ℂ Γ D) :
       DifferentiableOn ℂ (fun z => H (Γ z)) D
   ```

   This theorem is deliberately a finite-coordinate chart theorem, not an
   arbitrary-index API.  Its current production file is
   `BHWPermutation/SourceComplexLocalChart.lean`; the Gram-map pullback and
   source-variety identity principle live in
   `BHWPermutation/SourceComplexDensity.lean`, while the base germ structure,
   restriction, subtraction, continuity, and permutation-precomposition lemmas
   live in `BHWPermutation/SourceExtension.lean`.

   `sourceVariety_localChart_totallyReal_zero` now takes
   `SourceVarietyGermHolomorphicOn`.  The selected-chart theorem already
   exports `hΓvar`; this is exactly the missing equality domain for the germ
   representative.  No new Hall-Wightman theorem is hidden here.

5. In `BHWPermutation/SourceDistributionalUniqueness.lean`,
   `sourceDistributionalUniquenessSetOnVariety_of_realEnvironment` now sets
   `H := Φ - Ψ`, builds `hH` using
   `SourceVarietyGermHolomorphicOn.sub`, calls the germ local-chart theorem,
   then calls `sourceComplexGramVariety_identity_principle`.  The proof
   shape and mathematical content stay the same; only the analytic predicate
   is corrected.

Second, the archived ordinary pure-Gram `S'_n` seed package would have been
proved in the order documented below.  This list is retained only to explain
the source of the older theorem names and to keep the conditional
full-component fork auditable; it is not the active theorem-2 implementation
order:
`BHW.os45Figure24_sourceChart_at`,
`BHW.os45Figure24AdjacentLift_extendF_eq_permutedWick_zero`,
`BHW.os45SPrime_canonicalLift_pairing_eq_permutedSchwinger`,
`BHW.os45SPrime_sourcePullback_pairing_eq_acrPermutedBoundary`,
`BHW.os45SPrime_sourcePullback_pairing_eq_permutedSchwinger`,
`BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`,
`BHW.OS45SPrimeFigure24LocalSourceSeedData`,
`BHW.os45SPrime_figure24SourceEqOnUsrc_of_compactWickPairing`,
`BHW.os45SPrime_figure24LocalSourceSeedData_of_OSI45`,
`BHW.os45SPrime_figure24LocalSourceEq_of_seedData`,
`BHW.os45SPrime_figure24LocalSourceEq_of_BHWJost`,
`BHW.os45SPrime_figure24LocalBranchCompatibility_of_BHWJost`,
`BHW.os45SPrime_rawAdjacentWick_extendF_eq_identityWick_of_BHWJost`,
`BHW.os45SPrime_rawAdjacentWick_extendF_pairing_eq_permutedSchwinger`,
`BHW.os45SPrime_rawAdjacentWick_bvtF_pairing_eq_permutedSchwinger`,
`BHW.os45SPrime_rawAdjacentWick_extendF_pairing_eq_bvt_F`,
`BHW.os45SPrime_permutedWickExtendF_pairing_eq_permutedSchwinger`,
`BHW.os45AdjacentSPrimeScalarizationChart_of_figure24`,
`BHW.os45AdjacentSPrimeSourceEq_of_compactWickPairingEq`,
`BHW.os45AdjacentSPrimeScalarSeed_of_compactWickPairingEq`, and
`BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq`.  The
checked `BHW.os45AdjacentQuarterTurnScalarCorridor_of_figure24` may only be
called after that path-and-seed package exists.  None of these inputs may be
replaced by final real-edge equality, `AdjacentOSEOWDifferenceEnvelope`,
global PET branch independence, or a local boundary functional standing in
for `bvt_W`.

Source-decision compatibility guard for this whole adjacent list: the displayed
names are the pure-Gram version of the OS45 `S'_n` packet and are no longer
the active theorem-2 implementation names.  The strict proper-complex route
must rename and restate these consumers on the oriented API
(`SourceOrientedScalarRepresentativeData`,
`sourceOrientedMinkowskiInvariant`,
`sourcePermuteOrientedGram`, and the oriented double-domain); no theorem in
this list may remain as a pure-Gram wrapper around an oriented proof.  The
active replacement order is:

`BHW.os45AdjacentSPrimeOrientedScalarizationChart_of_figure24`,
`BHW.OS45CompactFigure24WickPairingEq`,
`BHW.sourceOrientedAdjacentTubeAnchor_of_compactWickPairingEq`,
`BHW.os45AdjacentSPrimeOrientedRealSeed_of_compactWickPairingEq`,
`BHW.os45AdjacentSPrimeOrientedSourceEq_of_realSeed`,
`BHW.os45AdjacentSPrimeOrientedScalarSeed_of_realSeed`,
`BHW.os45AdjacentSPrimeOrientedScalarSeed_of_compactWickPairingEq`,
`BHW.os45AdjacentSPrimeOrientedQuarterTurnMem_closure_of_figure24Path`,
`BHW.os45AdjacentSPrimeOrientedSeedFigure24Path`,
`BHW.os45AdjacentSPrimeOrientedSeedFigure24Path_of_compactWickPairingEq`,
`BHW.os45OneBranchOrientedSourceEq_sourceInput_id`,
`BHW.os45OneBranchOrientedSourceEq_sourceInput_adjacent`,
`BHW.os45OneBranchOrientedACRBHWAgreement_of_orientedScalarEq`,
`BHW.os45OneBranchOrientedACRBHWAgreement_of_orientedSourceEq`,
`BHW.os45BranchHorizontalSourceGermAt_of_orientedSourceEq`, and finally
`BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_id/adjacent`.
Every row in that replacement order consumes the oriented representative
`BHW.sourceOrientedScalarRepresentativeData_bvt_F`, not the ordinary
`BHW.sourceScalarRepresentativeData_bvt_F`.

The adjacent scalar-trace theorem has a non-circular upstream order.  First,
`BHW.os45Figure24AdjacentLift_extendF_eq_permutedWick_zero` is checked geometry:
using `BHW.figure24RotateAdjacentConfig_lorentz_inverse`,
`BHW.extendF_complex_lorentz_invariant`, `bvt_F_holomorphic`, and
`bvt_F_restrictedLorentzInvariant_forwardTube`, it rewrites the deterministic
canonical lift `hChart.adjLift x 0` to the raw adjacent Wick section under
`extendF` and gives the raw section ordinary-extended-tube membership.  This
normalization is not the boundary theorem and cannot replace it.

Second, the genuine OS-I §4.5/BHW/Jost boundary input is the compact
canonical-lift theorem
`BHW.os45SPrime_canonicalLift_pairing_eq_permutedSchwinger`.  Its proof must
build `φZ`, `ψZ := permuteZeroDiagonalSchwartz τ.symm φZ`, use
`bvt_euclidean_restriction` and, if needed, one `OS.E3_symmetric` call for
the zero-diagonal compact tests; then it must spell out the OS I equations
(4.1), (4.12), and (4.14), Bargmann-Hall-Wightman continuation, and Jost
real-environment uniqueness for the selected Figure-2-4 chart.  This theorem
is the source boundary gate.  It is not derived from
`BHW.os45SPrime_rawAdjacentWick_extendF_eq_identityWick_of_BHWJost` or from
any theorem that consumes local scalar source equality.

Third,
`BHW.os45SPrime_sourcePullback_pairing_eq_acrPermutedBoundary` and
`BHW.os45SPrime_sourcePullback_pairing_eq_permutedSchwinger` are mechanical
rewrites of the canonical theorem using
`hRep.branch_eq`, `hChart.adjLift_sourceGram`, and the checked
`bvt_euclidean_restriction` formula for `ψZ`.  Fourth,
`BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`
uses that source-pullback theorem plus the same finite permutation
change-of-variables calculation as
`os45_adjacent_euclideanEdge_pairing_eq_on_timeSector` to identify the raw
adjacent Wick trace pairing.  The public theorem
`integral_perm_eq_self` from `WickRotation/SchwingerAxioms.lean` is the
intended support for that change of variables; the private helper
`integral_perm_eq_self_locality` must not be imported or exposed.

Only after this adjacent trace theorem is available does the local scalar
source equality enter.  The equality
`BHW.os45SPrime_figure24LocalSourceEq_of_BHWJost` says that for
`Z = sourceMinkowskiGram d n (wick x)` on the selected source chart,
`hRep.Phi (sourcePermuteComplexGram n τ Z) = hRep.Phi Z`.  It is decomposed
into `BHW.OS45SPrimeFigure24LocalSourceSeedData`,
`BHW.os45SPrime_figure24LocalSourceSeedData_of_OSI45`, and
`BHW.os45SPrime_figure24LocalSourceEq_of_seedData`.  The seed-data structure
stores a nonempty relatively open scalar seed `Wseed`, a connected relatively
open scalar corridor `Wscal`, `Wseed ⊆ Wscal`,
`sourceMinkowskiGram '' hChart.Usrc ⊆ Wscal`, the double-domain inclusion for
`Wscal`, and equality of
`Z ↦ hRep.Phi (sourcePermuteComplexGram n τ Z)` with `hRep.Phi` on `Wseed`.
The producer first proves
`BHW.os45SPrime_figure24SourceEqOnUsrc_of_compactWickPairing` on
`hChart.Usrc`: its two scalar pullbacks are holomorphic by
`SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram` and
`hChart.double_mem`; their compact Wick-section pairings are compared by the
adjacent trace theorem above, the checked compact Wick equality
`os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`, and the identity Wick
scalarization from `hRep.branch_eq` plus `BHW.extendF_eq_on_forwardTube`.
Equality on `hChart.Usrc` follows by compact-support separation and
`eqOn_openConnected_of_eqOn_wickRealSection`.

After that chart equality is available, the seed data are constructed
without the later quarter-turn path.  Choose
`zreg ∈ hChart.Usrc` by
`BHW.exists_regular_sourcePoint_in_open_neighborhood`, whose proof is now
scratch-checked from
`(BHW.dense_sourceComplexGramRegularAt d n).exists_mem_open hU_open
⟨z0,hz0U⟩`; the returned order is
`⟨zreg, hzreg_regular, hzregU⟩`, so the exported witness is
`⟨zreg, hzregU, hzreg_regular⟩`.  Then take
`Gseed = sourceMinkowskiGram d n zreg`, and use
`BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular_allArity`
inside `hChart.Usrc` to obtain the relatively open scalar seed `Wseed`.
When descending source equality to `Wseed`, the exact checked call is
`have hsrc := hEq_src hzUsrc`, because `Set.EqOn` keeps the point argument
implicit; after `hW_realize G hG = ⟨z,hzUreg,hGz⟩`, use
`hzUsrc := hUreg_sub hzUreg` and close by `simpa [hGz] using hsrc`.
The source-chart construction's helper
`BHW.IsRelOpenInSourceComplexGramVariety.sourceMinkowskiGram_preimage_open`
is now pinned to a scratch-checked proof: unfold
`IsRelOpenInSourceComplexGramVariety`, use that every
`sourceMinkowskiGram d n z` lies in the full source Gram variety by
`⟨z, rfl⟩`, and take the preimage of the ambient open set by the existing
continuous map `(BHW.contDiff_sourceMinkowskiGram d n).continuous`.
The same chart block now pins
`BHW.exists_connected_sourceNeighborhood_with_wickPreimage`: set
`L := BHW.wickRealSectionLeftInverse d n`,
`W := Ω ∩ L ⁻¹' V`, choose a metric ball inside `W` by
`Metric.mem_nhds_iff`, take `Usrc` to be that ball, and set
`V0 := {x | wick x ∈ Usrc}`.  The complex ball is connected by
`isConnected_ball`; the real patch connectedness is the separate convexity
lemma `BHW.isConnected_wickPreimage_ball`, using real-affineness of
`x ↦ fun k => wickRotatePoint (x k)`.  Recover `V0 ⊆ V` from
`BHW.wickRealSectionLeftInverse_wickRotateRealConfig`, and store
`V0_connected` explicitly in `BHW.OS45Figure24SourceChartAt`; do not infer it
from connectedness of `Usrc`.
Set
`D = BHW.sourceDoublePermutationGramDomain d n τ` and
`Wscal = connectedComponentIn D Gseed`.  The rel-open field for `D` comes
from
`BHW.sourceDoublePermutationGramDomain_relOpen_of_sourceExtendedTubeGramDomain`
and `hRep.U_eq`; `Wscal` is relatively open by the checked
`BHW.sourceComplexGramVariety_connectedComponentIn_relOpen`, connected by
`isConnected_connectedComponentIn_iff.mpr`, and contained in `D` by
`connectedComponentIn_subset`.  `Wseed ⊆ Wscal` and
`sourceMinkowskiGram '' hChart.Usrc ⊆ Wscal` are both applications of
`IsPreconnected.subset_connectedComponentIn`: first to the connected scalar
seed, and then to the connected continuous image of `hChart.Usrc`.  The
quarter-turn Figure-2-4 scalar path remains a separate later obligation for
`BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq` and the
horizontal source-germ corridor; it is not an input to the raw Wick source
equality.

The propagation theorem `...LocalSourceEq_of_seedData` is then implementation-level:
it uses
`SourceVarietyGermHolomorphicOn.precomp_sourcePermuteComplexGram`,
`SourceVarietyGermHolomorphicOn.of_subset_relOpen`,
`SourceVarietyGermHolomorphicOn.sub`, and
`sourceComplexGramVariety_identity_principle` to propagate the seed equality
from `Wseed` to `Wscal`, then evaluates at
`sourceMinkowskiGram d n (wick x)` using `hChart.wick_mem` and
`chartGram_subset`.  It is not allowed to choose a second scalar function or
to infer off-variety equality of ambient extensions.
Once this source equality exists, the pointwise branch theorem
`BHW.os45SPrime_figure24LocalBranchCompatibility_of_BHWJost` then evaluates
this scalar equality with `SourceScalarRepresentativeData.branch_eq` on the
two ordinary extended-tube realizations `zraw` and `wick x`; its only extra
work is the algebra
`sourceMinkowskiGram d n zraw =
 sourcePermuteComplexGram n τ (sourceMinkowskiGram d n (wick x))` by
`sourceMinkowskiGram_perm`.  The local source theorem and its pointwise
evaluation must not call
`bvt_F_distributionalJostAnchor_of_OSII`,
`BHW.hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
or any global PET consumer; those belong to the later `S''_n` source package.
However, before the source equality above can be proved, the upstream compact trace
input must be established in the non-circular order now recorded in the
theorem-2 blueprint.  The canonical-lift theorem
`BHW.os45SPrime_canonicalLift_pairing_eq_permutedSchwinger` is the direct OS I
§4.5/BHW/Jost compact-boundary theorem for the deterministic Figure-2-4 lift.
Then `BHW.os45SPrime_sourcePullback_pairing_eq_permutedSchwinger` rewrites
that canonical theorem by `hRep.branch_eq` and `hChart.adjLift_sourceGram`;
`BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`
then performs the final `bvt_euclidean_restriction` and finite permutation
change of variables used in
`os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`.  No theorem in this
block may integrate an arbitrary existential `Δ_x`; the selected
Figure-2-4 chart must carry the canonical lift itself.  The currently private
helper `integral_perm_eq_self_locality` must not be imported by downstream
files; public permutation changes of variables should use
`integral_perm_eq_self` from `WickRotation/SchwingerAxioms.lean`.

Only after the adjacent trace theorem and local scalar source equality have
been proved do the raw adjacent-Wick theorems enter.  The local pointwise
branch comparison
`BHW.os45SPrime_rawAdjacentWick_extendF_eq_identityWick_of_BHWJost` evaluates
the propagated scalar equality by `hRep.branch_eq` on the two ordinary
extended-tube realizations.  Its wrapper proves the two sector-membership
hypotheses: the raw adjacent point is in the identity ordinary extended-tube
sector by Figure 2-4 and in the adjacent sector by the identity Wick
forward-tube field.  It is not the global PET-independence consumer
`BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry`; that theorem
may not be called to close this local gate.

The downstream compact theorems are then mechanical: the left-side raw compact
theorem follows from the pointwise branch comparison,
`extendF_eq_on_forwardTube` on the identity Wick branch,
`bvt_euclidean_restriction`, and one application of `OS.E3_symmetric`; the
right-side compact theorem follows by finite permutation change of variables
and `bvt_euclidean_restriction`; their composition is
`BHW.os45SPrime_rawAdjacentWick_extendF_pairing_eq_bvt_F`.  The raw adjacent
Wick point is still not known to lie in `AnalyticContinuationRegion d n 1`,
so this comparison must not be interpreted as pointwise agreement of
`extendF` with an ACR branch at the raw adjacent point.

The pointwise raw-adjacent/identity-Wick `extendF` branch comparison comes
later from the local scalar source equality, not directly from the OS-I §4.5
compact theorem.  The exact OS sequence
identity-Wick ACR boundary selection for `ψZ` -> optional E3 symmetry if the
proof is oriented through `φZ` -> equations (4.1), (4.12), and (4.14) ->
symmetric analytic continuation to the permuted tube ->
Bargmann-Hall-Wightman continuation -> Jost real-environment uniqueness is
the source of the canonical-lift compact theorem above.  The local source
equality turns that compact trace input into equality of the scalar
representative on the connected source chart; only then may
`SourceScalarRepresentativeData.branch_eq` be evaluated at the raw adjacent
ordinary-extended-tube point and the identity Wick point.  The raw adjacent
section enters through Figure-2-4 ordinary extended-tube membership, not
through ACR membership.
None of these steps may be proved by constructing a completed
`WightmanFunctions` object and using the existing `W_analytic_BHW` package,
because that package consumes `Wfn.locally_commutative`, the theorem-2 output.
The raw comparison also must not be closed by calling the global PET
branch-independence consumer
`BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry`; it stays
specialized to the selected Figure-2-4 chart and depends on the already
established local scalar equality.
Do not give the raw comparison theorem, the raw Schwinger-valued theorem, or
the canonical-lift theorem an unused
`hRep : SourceScalarRepresentativeData ...` hypothesis.  The existing helpers
`BHW.extendF_eq_boundary_value`, `BHW.extendF_eq_boundary_value_ET`, and
`BHW.extendF_eq_on_forwardTube` do not close this gate at
`permAct τ (wick x)`: those helpers apply to real-embedded boundary points or
ordinary forward-tube points, while the adjacent Wick section is a complex
ordinary-extended-tube point selected by Figure-2-4 and is not supplied as an
ACR(1) point by the existing trace-membership API.  Therefore the specialized
canonical-lift compact theorem, not the raw pointwise theorem, remains the
exact OS-I §4.5/BHW/Jost mathematical source obligation before any adjacent
`S'_n` production Lean.

For the path package, the exact Lean topology API is now pinned.  In the
finite-dimensional source space, use
`(IsOpen.isConnected_iff_isPathConnected hUsrc_open).mp hUsrc_conn` to turn
the open connected source chart `Usrc` into `IsPathConnected Usrc`; use
`IsPathConnected.joinedIn` to get a `JoinedIn Usrc zreg zwick0`; extract the
configuration path by `JoinedIn.somePath` and keep membership by
`JoinedIn.somePath_mem`.  Push this path forward with `Path.map` along the
globally continuous `sourceMinkowskiGram` map.  Concatenate the resulting
scalar path to the Figure-2-4 scalar path with `Path.trans` (method form
`γseed.trans γfig`); range control for the concatenated path is exactly
`Path.trans_range`, or equivalently two applications of `JoinedIn.trans` if
the proof is phrased as joined-in data.  Do not cite an unspecified "path
concatenation lemma" here.

Local API audit, 2026-05-01: the names in the preceding paragraph have been
checked against the local Mathlib tree.  A scratch Lean check shows that a
standalone support file also needs `Mathlib/Analysis/Complex/Basic.lean`; with
only the locally-convex and path imports, Lean does not synthesize
`TopologicalSpace (Fin n -> Fin (d + 1) -> ℂ)`.  The exact files are:
`Mathlib/Analysis/Complex/Basic.lean` for the complex topology,
`Mathlib/Analysis/LocallyConvex/WithSeminorms.lean` for the
`NormedSpace.toLocallyConvexSpace` instance that lets
`LocallyConvexSpace ℝ (Fin n -> Fin (d + 1) -> ℂ)` synthesize; the same
import brings in `Mathlib/Topology/Algebra/Module/LocallyConvex.lean`, where
`LocallyConvexSpace.toLocPathConnectedSpace` supplies
`LocPathConnectedSpace (Fin n -> Fin (d + 1) -> ℂ)`,
`Mathlib/Topology/Connected/LocPathConnected.lean` for
`IsOpen.isConnected_iff_isPathConnected`,
`Mathlib/Topology/Connected/PathConnected.lean` for
`JoinedIn.somePath`, `JoinedIn.somePath_mem`, and `JoinedIn.trans`, and
`Mathlib/Topology/Path.lean` for `Path.trans` and `Path.trans_range`.  If the
archived overlap-cover connectedness proof is ever revived, the checked
connected-union theorem is
`IsConnected.biUnion_of_reflTransGen` in
`Mathlib/Topology/Connected/Basic.lean`; its Lean signature requires an
explicit nonempty index set `t.Nonempty` and a relation of the form
`ReflTransGen (fun i j => (s i ∩ s j).Nonempty ∧ i ∈ t) i j`.  Therefore the
proof docs must not say merely "the connected union theorem applies": they
must provide the active-label nonemptiness and the exact intersection graph
relation if this package becomes active.
Scratch Lean check, 2026-05-02: with imports
`Mathlib.Analysis.Complex.Basic`,
`Mathlib.Analysis.LocallyConvex.WithSeminorms`,
`Mathlib.Topology.Connected.LocPathConnected`,
`Mathlib.Topology.Connected.PathConnected`, and `Mathlib.Topology.Path`, the
exact code
`(IsOpen.isConnected_iff_isPathConnected hUsrc_open).mp hUsrc_conn`,
`hUsrc_path.joinedIn zreg hzregUsrc zwick0 hzwickUsrc`,
`let γsrc : Path zreg zwick0 := hjoin.somePath`,
`have hγsrc_mem : ∀ t, γsrc t ∈ Usrc := hjoin.somePath_mem`, and
`Path.trans_range γseed γfig` elaborates.  Thus this topology segment is
checked support.  It does not make
`BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq` production
ready, because the source seed/provenance theorem and scalar double-domain
realization are still the mathematical inputs.

For the adjacent `S'_n` source-equality theorem, the exact analytic API is
also pinned.  Pulling a scalar representative back to `Usrc` uses the germ
signature
`BHW.SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram hPhi hGramU`, where
`hGramU : sourceMinkowskiGram d n '' Usrc ⊆ hRep.U` for the identity branch
and
`hGramU : sourceMinkowskiGram d n '' Usrc ⊆
{Z | sourcePermuteComplexGram n τ Z ∈ hRep.U}` for the adjacent branch.  The
Figure-2-4 source chart must export both the forward Wick membership
`∀ x ∈ V0, (fun k => wickRotatePoint (x k)) ∈ Usrc` and the reverse
real-section equivalence
`∀ x, (fun k => wickRotatePoint (x k)) ∈ Usrc ↔ x ∈ V0`; the latter is what
feeds the last hypothesis of `eqOn_openConnected_of_eqOn_wickRealSection`.
The required continuity of the real Wick section must be exposed as the public
helper `BHW.continuous_wickRotateRealConfig`.  This is now checked in
`OSToWightmanLocalityOS45BHWJost.lean` by the same coordinatewise proof as
the old private helper in `OSToWightmanTubeIdentity.lean`.

The theorem-2 blueprint now names the two implementation data carriers that
must exist, or be kept as local variables with the same fields:
`BHW.OS45Figure24SourceChartAt`, carrying `V0`, `Usrc`, Wick membership,
`V0_connected`, Wick real-section equivalence, double-domain membership,
forward-tube membership of the identity Wick branch, and the deterministic fields
`adjLift`, `adjLift_mem_extendedTube`, and `adjLift_sourceGram` for the
canonical rotated Figure-2-4 adjacent lift; and
`BHW.OS45AdjacentSPrimeScalarSeedWithSourceProvenance`, carrying the scalar
seed together with `Usrc`, `zreg`, `Gseed`, `hwick_mem`, `V0_connected`,
`zreg ∈ Usrc`, and the source-level double-domain field needed by the path
segment.  These are not substitute theorem routes; they are
provenance-preserving forms of the same OS I §4.5 / BHW seed proof.

The source-chart constructor
`BHW.os45Figure24_sourceChart_at` must consume the actual Figure-2-4
path-stability field from the checked selector, not merely the ordered/Jost
facts for an arbitrary `V`.  For the scalarization/source-pairing theorem its
input is the canonical field
`hV_adjLift_ET : ∀ x ∈ V, ∀ t,
BHW.os45Figure24AdjacentLift hd τ x t ∈ ExtendedTube`; the scalar-Gram
identity is the public algebraic theorem
`BHW.os45Figure24AdjacentLift_sourceGram`.  These two facts prove that the
base Wick source Gram lies in the adjacent double scalar domain before the
connected source neighborhood is chosen, and they give the deterministic lift
used under the compact pairing.  The separate closure-level existential
`hV_figPath_closure` is still needed later for the scalar corridor path, but
it is not the integrand supplier.  The topology shrink is then Lean-ready: use
the explicit `BHW.wickRealSectionLeftInverse`,
`BHW.continuous_wickRealSectionLeftInverse`,
`BHW.continuous_wickRotateRealConfig`, and
`BHW.exists_connected_sourceNeighborhood_with_wickPreimage`; set
`V0 := {x | wick x ∈ Usrc}` so the reverse real-section equivalence is
definitionally available, and prove/store `V0_connected` by
`BHW.isConnected_wickPreimage_ball`.  This is part of the chart data because
the later common-boundary envelope consumes connectedness of the real patch
itself.

Local code audit after checkpoint `996ebc1` (2026-05-01): the checked
Figure-2-4 support in
`OSToWightmanLocalityOS45Figure24.lean` currently provides the selector
theorems
`BHW.swFigure24_adjacentPathStableNeighborhood_exists`,
`BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability`,
`BHW.os45_adjacent_identity_horizontalEdge_sourcePatch`, and the oriented
path/source-patch strengthening.  It now also provides the deterministic lift
declarations `BHW.os45Figure24AdjacentLift`,
`BHW.continuous_os45Figure24AdjacentLift`,
`BHW.os45Figure24AdjacentLift_sourceGram`, and
`BHW.swFigure24_adjacentPathStableCanonicalLift_exists`.  It now also provides
the canonical source-patch carrier declarations
`BHW.OS45Figure24CanonicalSourcePatchData`,
`BHW.OS45Figure24OrientedCanonicalSourcePatchData`,
`BHW.exists_os45_adjacent_identity_canonicalSourcePatch_with_orientedPath`,
and the two `noncomputable def` selectors
`BHW.os45_adjacent_identity_canonicalSourcePatch_with_orientedPath` and
`BHW.os45_adjacent_identity_canonicalSourcePatch`.  It still does not provide
production declarations for `BHW.OS45Figure24SourceChartAt`, so the adjacent
`S'_n` proof docs must keep the chart promotion as an explicit pre-Lean task.
A later Lean port may not substitute an arbitrary choice of adjacent lift under
the compact integral.

The lift portion of the promotion proof is now checked.  It defines
`BHW.os45Figure24AdjacentLift hd τ x t` as
`BHW.figure24RotateAdjacentConfig hd
  (BHW.permAct τ (BHW.os45Figure24IdentityPath x t))`.  Its continuity is
`BHW.continuous_figure24RotatedIdentityPath` by `simpa`, and its source-Gram
identity is the three-line calculation:
apply `BHW.figure24RotateAdjacentConfig_lorentz_inverse`, rewrite the source
Gram by `BHW.sourceMinkowskiGram_complexLorentzAction`, and finish with
`BHW.sourceMinkowskiGram_perm`.  Then promote the checked compact-open proof to
`BHW.swFigure24_adjacentPathStableCanonicalLift_exists`, whose output contains
the deterministic field
`∀ x ∈ Upath, ∀ t, BHW.os45Figure24AdjacentLift hd τ x t ∈
BHW.ExtendedTube d n` and the identity-path scalar-Gram field with
`Γ := BHW.os45Figure24IdentityPath x`, conditional on the identity ordered
sector needed to keep `Γ` in the forward tube.  This theorem repeats the
existing compact-parameter neighborhood proof but exposes the actual map `H`;
it is not a wrapper around an arbitrary existential `Δ`.

The selector-to-chart carrier is now fixed as
`BHW.OS45Figure24CanonicalSourcePatchData`.  The checked implementation proves
the stronger oriented existential packet in `Prop` and then exposes the
oriented packet and its pure canonical projection by `noncomputable def`; this
is the required Lean shape for choosing data from upstream existence theorems.
It repeats the checked source-patch shrink, but starts from
`BHW.swFigure24_adjacentHorizontalEnvironmentWithRotatedPathStability` and the
corrected two-point contact segment construction.  It stores
deterministic lift membership
`∀ x ∈ V, ∀ t, BHW.os45Figure24AdjacentLift hd τ x t ∈ ExtendedTube`, a
closure-level Figure-2-4 scalar path whose adjacent realization is exactly
`BHW.os45Figure24AdjacentLift`, and the contact fields
`xseed_mem`, `xcontact_mem`, and
`xcontact = os45CommonEdgeRealPoint 1 xseed`.  It also keeps the Wick, real,
opposite-tube branch-geometry, pulled-branch, and closure oriented-path fields
needed by the next source-chart promotion.

New route correction for the adjacent scalarization chart: the Figure-2-4
hypothesis
`(fun k => x (τ k)) ∈ EuclideanOrderedPositiveTimeSector τ` does not imply
`(fun k => wickRotatePoint (x (τ k))) ∈ BHW.ForwardTube d n`.  Because
`EuclideanOrderedPositiveTimeSector τ` already applies a further `τ`
relabeling, and an adjacent swap is self-inverse, the standard theorem
`wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector` applied to that
hypothesis returns the identity Wick trace, not the adjacent raw Wick trace.
Therefore `BHW.OS45Figure24SourceChartAt` must not contain a
`wick_tau_forwardTube` field, and
`BHW.os45AdjacentSPrimeScalarizationChart_of_figure24` must not prove its
adjacent Wick identity by `SourceScalarRepresentativeData.branch_eq` followed
by `BHW.extendF_eq_on_forwardTube` at `wick (x ∘ τ)`.

The genuine missing theorem is now named explicitly:
`BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`.  It
must prove, on the Figure-2-4 source chart, equality of compact pairings
between the permuted source pullback
`x ↦ hRep.Phi (sourcePermuteComplexGram n τ
(sourceMinkowskiGram d n (fun k => wickRotatePoint (x k))))`
and the OS-II adjacent Wick trace
`x ↦ bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k)))`.  The pointwise
version is not an input to the seed proof; using it there is circular because
it already asserts the adjacent `S'_n` scalarization on the Wick real section.
Its proof must not pass through the specialized pointwise raw branch
comparison
`BHW.os45SPrime_rawAdjacentWick_extendF_eq_identityWick_of_BHWJost`: that
theorem consumes the chart-local source equality whose proof needs the
adjacent trace theorem, so using it here would be circular.  The upstream
non-mechanical input is instead the deterministic canonical-lift compact
theorem
`BHW.os45SPrime_canonicalLift_pairing_eq_permutedSchwinger`, proved directly
from OS I §4.5 equations (4.1), (4.12), and (4.14), Euclidean symmetry on
the compact test `ψZ`, the BHW continuation of the symmetric adjacent branch,
and Jost real-environment uniqueness on the selected Figure-2-4 chart.  Then
derive
`BHW.os45SPrime_sourcePullback_pairing_eq_permutedSchwinger` by
`hRep.branch_eq` and `hChart.adjLift_sourceGram`, and only after that apply
the final finite permutation change of variables to identify the adjacent
Wick trace pairing.

The ordinary continuity/measurability side of the canonical-lift compact
theorem is no longer an unnamed gap.  The theorem-2 blueprint now gives the
Lean-shaped proof of
`ContinuousOn (fun x => extendF (bvt_F OS lgc n) (hChart.adjLift x 0))
hChart.V0`: transport `bvt_F_holomorphic` and
`bvt_F_complexLorentzInvariant_forwardTube` across `BHW_forwardTube_eq`, take
`(BHW.extendF_holomorphicOn n (bvt_F OS lgc n) ...).continuousOn`, compose
`hChart.adjLift_continuousOn` with `x ↦ (x, 0)` into
`hChart.V0 ×ˢ Set.univ`, and use
`hChart.adjLift_mem_extendedTube` as the `MapsTo` proof.  This is ordinary
analytic bookkeeping only; the remaining adjacent source-boundary content is
the compact OS-I §4.5/BHW/Jost equality itself.

The Jost/Ruelle source theorem used in that compact equality has also been
re-pinned to the local scanned source.  In
`references/general-theory-of-quantized-fields.pdf`, PDF page `83` (printed
pages `150`--`151`), Appendix II proves uniqueness for two single-valued
`L_+(ℂ)`-invariant analytic branches on adjacent/permuted tube domains when
their real-boundary distributions agree; its generalized form allows the
real-intersection hypothesis in spacetime dimension greater than two.  The
theorem-2 route uses exactly the compact-test specialization: the OS-I
adjacent branch from (4.1), (4.12), and (4.14) has the same Figure-2-4 real
Jost boundary distribution as the ordinary BHW branch, so Jost/Ruelle
uniqueness identifies the two branches on the component containing the
canonical lift, and the adjacent boundary pairing is `OS.S n ψZ` by the same
zero-diagonal compact-test symmetry.  This is still a genuine source theorem
frontier, not a license to call raw adjacent pointwise equality, final
locality, or Streater-Wightman Theorem 3-6.

The theorem-2 blueprint now removes the last schematic `?osi45...` marker
from the canonical-lift compact theorem.  The source boundary gate is pinned
to two implementation-level pieces.  First,
`BHW.JostRuelleCompactBoundaryData` is the OS-free generic carrier for the
Ruelle/Jost uniqueness theorem: it stores a connected analytic branch domain,
the compact lift, the ordinary and adjacent analytic branches, their
holomorphy and complex-Lorentz invariance on that domain, a real Jost patch
with common boundary distribution, and the support-level fact that the lift
lies in the analytic domain wherever the compact test can contribute.
`BHW.OS45CanonicalAdjacentBranchBoundaryData` is the OS-specific/proof-local
carrier for one compact test: it stores the exact `φZ`, `ψZ`, the generic
Jost/Ruelle data `jr`, the equality between `jr.lift` and the deterministic
Figure-2-4 lift, equality of `jr.ordinaryBranch` with
`extendF (bvt_F OS lgc n)` on that lift, and the adjacent lift pairing
`= OS.S n ψZ`.  The adjacent branch packet feeding this carrier also stores
the OS-I real Jost boundary comparison
`adjacent_realBoundary_eq_ordinary`; without that field the later
real-boundary theorem would be false for an arbitrary analytic branch.  Its
only allowed producer is
`BHW.os45CanonicalAdjacentBranchBoundaryData_of_OSI45`, proved from OS I
§4.5 equations (4.1), (4.12), and (4.14), the compact zero-diagonal Euclidean
symmetry, BHW continuation, and the selected Figure-2-4 Jost real-boundary
comparison.  This producer is still a genuine source proof obligation, not a
wrapper around the canonical theorem.

Second, the generic theorem
`BHW.jostRuelle_uniqueContinuation_compactBoundary` now has an explicit
Lean-facing signature: from `JostRuelleCompactBoundaryData` alone it proves
equality of the ordinary and adjacent lift pairings by Ruelle/Jost uniqueness
on the connected component containing the real Jost patch and the compact
lift.  It is a standard complex-analytic/Jost theorem with no OS, PET, EOW,
scalar representative, locality, or `bvt_W` content.  The proof transcript is
now split into two OS-free analytic substeps:
`BHW.jostRuelle_realPatch_eqOn_of_distributionEq`, which turns
`D.realBoundary_eq` into pointwise equality on `D.jostPatch` by
`SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` and
the continuity of the two holomorphic branches restricted along
`BHW.realEmbed`, and
`BHW.jostRuelle_branch_eqOn_connectedDomain`, which applies
`BHW.identity_theorem_totally_real_product` to the holomorphic difference on
the connected domain `D.Ω`.  The compact theorem then uses pointwise support
reduction: if `(φ : NPointDomain d n -> ℂ) x = 0` both integrands vanish,
and otherwise `Function.mem_support.mpr` plus `subset_tsupport _` gives
`x ∈ tsupport φ`, so `D.lift_mem_of_support` and the connected-domain branch
identity compare the two branch values at `D.lift x`.  The integral equality
is then `MeasureTheory.integral_congr_ae`.  With these pieces, the public
`BHW.os45SPrime_canonicalLift_pairing_eq_permutedSchwinger` proof is the
mechanical composition:
ordinary lift integrand rewrite by `D.ordinary_eq_extendF_on_lift`, generic
Jost/Ruelle lift-pairing equality applied to `D.jr` and rewritten by
`D.jr_lift_eq`, then
`D.adjacent_lift_pairing_eq_permutedSchwinger`.  Therefore the adjacent
`S'_n` proof docs are more precise, but still not production-Lean-ready until
both `BHW.os45CanonicalAdjacentBranchBoundaryData_of_OSI45` and the generic
Jost/Ruelle compact theorem are proved or replaced by an already checked
sorry-free support theorem with the same mathematical content.

The API instantiation for the generic Jost/Ruelle theorem is now pinned in
the blueprint.  In
`BHW.jostRuelle_realPatch_eqOn_of_distributionEq`, set
`g x := D.ordinaryBranch (BHW.realEmbed x)` and
`h x := D.adjacentBranch (BHW.realEmbed x)`, prove
`ContinuousOn g D.jostPatch` and `ContinuousOn h D.jostPatch` by composing
`D.ordinary_holo.continuousOn` and `D.adjacent_holo.continuousOn` with the
continuous real embedding, and feed `D.realBoundary_eq` directly to
`SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`.
If the theorem is placed in a lower BHW module, the real-embedding
continuity must be proved locally or moved downward; the proof must not
import the Figure-2-4 support file merely to use
`BHW.continuous_realEmbedNPoint`.  In
`BHW.jostRuelle_branch_eqOn_connectedDomain`, set
`H z := D.ordinaryBranch z - D.adjacentBranch z`, use
`D.ordinary_holo.sub D.adjacent_holo`, turn the real-patch equality into
`H (BHW.realEmbed x) = 0` by `sub_eq_zero.mpr`, and apply
`BHW.identity_theorem_totally_real_product` with
`D.Ω_open`, `D.Ω_connected`, `D.jostPatch_open`,
`D.jostPatch_nonempty`, and `D.jostPatch_realEmbed_mem`.

Canonical-lift production readiness is now a four-part gate, not a theorem
name.  First build the exact zero-diagonal compact tests
`φZ` and `ψZ := permuteZeroDiagonalSchwartz τ.symm φZ`, with the orientation
checked by `bvt_euclidean_restriction` and at most one `OS.E3_symmetric`
call.  The theorem surfaces at this gate must carry the checked Figure-2-4
real-embedding hypotheses
`∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n` and
`∀ x ∈ V, BHW.realEmbed (fun k => x τ k) ∈ BHW.ExtendedTube d n`, with
`τ := Equiv.swap i ⟨i.val + 1, hi⟩`; these come from the local source patch
and are not to be inferred from bare `JostSet` membership.  Second prove
`BHW.os45CanonicalAdjacentBranchBoundaryData_of_OSI45` from OS I §4.5
equations (4.1), (4.12), and (4.14), Euclidean symmetry of `ψZ`, BHW
continuation, and the Figure-2-4 real Jost boundary comparison.  The producer
must now be assembled from the Lean-facing packets named in the
blueprint: `BHW.OS45Figure24JostRuelleDomainData`,
`BHW.OS45Figure24OrdinaryBranchData`,
`BHW.OS45Figure24AdjacentBranchData`, and the mechanical extraction
`BHW.os45Figure24_realBoundaryEq_of_OSI45`.  The domain packet exports the
load-bearing field `Ω ⊆ BHW.ExtendedTube d n`; the ordinary branch packet is
then definitionally the actual restriction of
`BHW.extendF (bvt_F OS lgc n)` to `Ω`, with differentiability from
`BHW.extendF_holomorphicOn.mono` and Lorentz invariance from the checked
`BHW.extendF_complex_lorentz_invariant`, using
`bvt_F_restrictedLorentzInvariant_forwardTube`.  This replaces the older
tautological ordinary-branch line and prevents the producer from silently
introducing a second ordinary analytic branch.  The adjacent branch packet
must carry the OS-I branch's holomorphy, Lorentz invariance, compact lift
pairing `= OS.S n ψZ`, and the real-boundary provenance field
`adjacent_realBoundary_eq_ordinary`; the theorem
`BHW.os45Figure24_realBoundaryEq_of_OSI45` only rewrites this field through
`Dord.ordinaryBranch_def`.  The final producer then fills all `D.jr` branch,
Lorentz-invariance, real-boundary, lift-support, and adjacent pairing fields
from these packets.  Third prove the OS-free
`BHW.jostRuelle_uniqueContinuation_compactBoundary` through
`BHW.jostRuelle_realPatch_eqOn_of_distributionEq` and
`BHW.jostRuelle_branch_eqOn_connectedDomain`.  Fourth derive the public
canonical theorem only by rewriting the ordinary lift integrand with
`D.ordinary_eq_extendF_on_lift`, using pointwise support reduction through
`Function.mem_support.mpr` and `subset_tsupport _`, applying the generic
Jost/Ruelle equality to `D.jr`, rewriting by `D.jr_lift_eq`, and finishing
with `D.adjacent_lift_pairing_eq_permutedSchwinger`.
Any dependency on `SourceScalarRepresentativeData`,
`BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`,
`BHW.os45SPrime_figure24LocalSourceEq_of_BHWJost`, the raw pointwise
comparison, final `bvt_W` locality, `AdjacentOSEOWDifferenceEnvelope`, or
global PET branch independence means this gate has not been proved on route.

The theorem-2 blueprint now includes the Lean-shaped record constructor for
`BHW.os45CanonicalAdjacentBranchBoundaryData_of_OSI45`: define `τ`, `φZ`,
`ψZ`; build `DΩ`, `Dord`, and `Dadj`; extract `hreal` from
`Dadj.adjacent_realBoundary_eq_ordinary`; construct
`JostRuelleCompactBoundaryData`; then fill `jr_lift_eq`,
`ordinary_eq_extendF_on_lift`, and
`adjacent_lift_pairing_eq_permutedSchwinger` by the corresponding packet
fields.  The only non-mechanical subproducer left inside this assembly is the
OS-I/BHW continuation theorem
`BHW.os45_bhwJostContinuation_adjacentPermutedBranch`, whose output record
`BHW.OS45AdjacentBHWJostContinuationData` stores the branch `Badj`, its
holomorphy and Lorentz invariance on `DΩ.Ω`, real-boundary equality for all
compact tests on `hChart.V0`, and the fixed canonical-lift pairing for `φ`.
The blueprint further decomposes its proof through
`BHW.os45_BHWJost_continue_adjacentBranch_from_OSI45`: continue
`Dinit.branchτ` from
`Dinit.Ωτ = BHW.permutedExtendedTubeSector d n Dinit.τ` to `DΩ.Ω`, transport
Lorentz invariance from `Dlor`, prove the real-boundary distributional
comparison for every compact `χ` on `hChart.V0`, and transport
`Dinit.branchτ_boundary_pairing` to `x ↦ hChart.adjLift x 0`.  This lower
theorem is exactly the formal OS I §4.5/BHW continuation input; it must not
mention source representatives, EOW, PET monodromy, `bvt_W`, or final
locality.

Latest adjacent-continuation refinement, 2026-05-02: the lower theorem is now
split once more through the local carrier
`BHW.OS45BHWJostLocalContinuationData` and producer
`BHW.os45_BHWJostLocalContinuationData_from_OSI45`.  This is the first genuine
Lean target inside the adjacent BHW/Jost packet.  It must construct the local
proper-complex Lorentz/Jost hull for the identity and selected adjacent tube,
prove openness, connectedness, and membership for the whole initial adjacent
tube `Dinit.Ωτ`, `DΩ.Ω`, the adjacent Wick edge, the real Jost patch, and the
deterministic lift
`x ↦ hChart.adjLift x 0`, and then obtain the analytic branch `WJ` with:
holomorphy on the hull, complex-Lorentz invariance on the hull, agreement with
`Dinit.branchτ` on all of `Dinit.Ωτ` and hence on the selected adjacent Wick
edge, equality of ordinary and
continued boundary-value distributions on every compact test supported in
`hChart.V0`, and the compact lift pairing equal to `OS.S n ψZ`.

Latest adjacent-hull/real-boundary refinement, 2026-05-02: the local hull is
now fixed as a path component, not an unnamed connected open set.  Define the
ambient domain as the union of proper-complex Lorentz images of
`BHW.ExtendedTube d n` and of the selected adjacent sector
`BHW.permutedExtendedTubeSector d n Dinit.τ`; choose
`zτ0 := fun k => wickRotatePoint (x0 (Dinit.τ k))`; set
`ΩJ := pathComponentIn Ambient zτ0`.  The proof uses the checked local helper
`BHW.isOpen_pathComponentIn_of_isOpen_normed` for openness, the component
path-connectedness API, `IsOpen.isConnected_iff_isPathConnected`,
`JoinedIn.trans`, and `JoinedIn.mono`.  The two nontrivial joining inputs are now named:
`os45Figure24_joined_adjacentWick_to_adjLift0`, using
`figure24RotateAdjacentConfig_lorentz_inverse` and a path in the proper
complex Lorentz group, and
`os45Figure24_joined_adjLift0_to_realPatch`, using the deterministic
Figure-2-4 lift path.  This pins `Dinit.Ωτ ⊆ ΩJ` and `DΩ.Ω ⊆ ΩJ` without
global PET independence.

The real-boundary equality is also no longer a black-box phrase.  For every
fresh compact test `χ` supported in `hChart.V0`, the proof must build fresh
zero-diagonal data `χZ` and `ψχZ`, construct the corresponding initial
adjacent branch datum from `(4.1)/(4.12)`, and use `(4.14)` through the
Lorentz-invariant branch packet.  The comparison of `WJ (realEmbed x)` with
the swapped ordinary branch is pointwise on the real patch, from
`WJ = Dinit.branchτ` on `Dinit.Ωτ`,
`Dinit.branchτ_eq_correctedExtendF`, and the swapped real-embedding
membership `hV_swapET`.  The remaining compact equality is exactly the
OS I §4.5 Figure-2-4 branch-difference theorem
`BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45`.  If
the producer is implemented in a different file, its signature must carry the
chart-produced source-patch fields needed by that theorem: `V` open,
`V ⊆ os45Figure24SourcePatch`, and the closure-level
`OS45Figure24OrientedPathField` on `hChart.V0`.  It must not use the later
generic `jostRuelle_uniqueContinuation_compactBoundary`, scalar
representatives, PET independence, or final `bvt_W` locality.

The proof-doc name
`BHW.os45BHWJostHull d n Dinit.τ
  (fun k => wickRotatePoint (x0 (Dinit.τ k)))`
is only a local name for this OS I §4.5/Bargmann-Hall-Wightman path component.
Production Lean may spell it with an existing local BHW continuation-domain
API if the same fields are proved, but it may not be replaced by global PET
independence, an EOW envelope, final locality, or a scalar-representative
theorem.  Until this carrier theorem has a checked implementation or an
already checked support theorem with exactly these fields, the adjacent branch
packet is not production-Lean-ready.

After the route-cycle correction, the upstream carrier must split before
Lean into the direct pair-data surfaces:
`BHW.os45_BHWJostHullData_of_figure24` for the local open connected hull and
all Wick/real source membership fields,
`BHW.os45_BHWJostBranch_onLocalHull_of_OSI45` for the BHW continued adjacent
branch and its agreement with `Dinit.branchτ` on all of `Dinit.Ωτ`,
`BHW.OS45SourcePatchBHWJostPairData` and
`BHW.os45_sourcePatch_bhwJostPairData_on_figure24SourcePatch_of_OSI45` for the ordinary/adjacent
branch pair and their Wick/real trace formulas,
the checked `P.difference` field for the single holomorphic
adjacent-minus-ordinary branch difference on the selected hull, and the
OS-I/BHW-Jost proof that this checked difference branch is distributionally
zero on compact tests supported in the selected source patch.  The real-trace
translation and compact-pairing algebra are now checked in Lean through
`BHW.realSourceBranchDifference_zero_of_pairData_difference_zero`,
`BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero`, and the
family/source-anchor consumers.  A separate
`OS45SourcePatchBHWJostDifferenceData` wrapper is no longer a first target
unless it carries new source provenance not already present in `P` and
`P.difference`.  Only after the public source-patch compact theorem is
assembled may the downstream full continuation package add
`BHW.os45_BHWJostRealBoundaryEq_of_OSI45`,
`BHW.os45_BHWJostLiftTransport_onSupport_of_OSI45`, and
`BHW.os45_BHWJostLiftPairing_of_OSI45`.

The later transport theorem is not a bare endpoint identity: the checked lift
is the rotated two-plane realization.  It must use
`BHW.figure24RotateAdjacentConfig_lorentz_inverse`, `hChart.adjLift_def`,
`BHW.os45Figure24IdentityPath_zero`, `WJ`'s Lorentz invariance on `ΩJ`, and
`WJ = Dinit.branchτ` on `Dinit.Ωτ` to identify the lift value with the
adjacent Wick edge on `tsupport φ`.  Hiding this Lorentz-transport equality
inside an integral rewrite would leave the proof docs incomplete.

The local BHW branch theorem used in this carrier is now pinned to the
Hall-Wightman Lemma-1 proof shape: prove local constancy of
`A ↦ Dinit.branchτ (complexLorentzAction A z)` in complex Lorentz group
charts by real-Lorentz invariance and the totally-real identity theorem; cover
proper-complex Lorentz paths by finitely many such charts; prove
single-valuedness for two representations of the same hull point using the
Hall-Wightman curve/scalar-product construction; define `WJ` by a
choice-independent chain; obtain holomorphy from the final chart and
Lorentz-invariance by chain extension.  This is still a genuine lower BHW
support theorem, not a wrapper and not a global PET-independence call.

Canonical producer implementation ledger.  This table is the checkpoint
against wrapper drift: the checked Euclidean edge theorem is a real input, but
it is not the adjacent analytic branch producer.

| Piece | Current status | Allowed inputs |
| --- | --- | --- |
| Zero-diagonal compact-test orientation | Checked local Lean input. | `zeroDiagonal_of_tsupport_subset_jostOverlap`, `permuteZeroDiagonalSchwartz`, `bvt_euclidean_restriction`, and one `OS.E3_symmetric` call. |
| `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector` | Checked local Lean input for the Euclidean edge equality on ordered sectors. | Its public theorem statement; do not depend on the private helper `integral_perm_eq_self_locality` outside `OSToWightmanLocalityOS45.lean`. |
| `BHW.OS45Figure24JostRuelleDomainData` and `BHW.os45Figure24_jostRuelleDomainData_of_chart` | Lean-shaped proof pinned; production Lean not started. | Choose `Ω := BHW.ExtendedTube d n`; use `BHW.isOpen_extendedTube`, `BHW.isConnected_extendedTube`, `hV_ET`, and `hChart.adjLift_mem_extendedTube`.  The swapped real-embedding field remains on the surrounding canonical surface for adjacent-source use, but this domain constructor must not infer extended-tube membership from bare `JostSet` membership or choose a second domain. |
| `BHW.OS45Figure24OrdinaryBranchData` and `BHW.os45Figure24_ordinaryBranchData_of_bvt_F` | Transcript pinned but production Lean not started; mechanically ready after domain data. | `bvt_F_holomorphic`, `bvt_F_complexLorentzInvariant_forwardTube`, `bvt_F_restrictedLorentzInvariant_forwardTube`, `BHW.extendF_holomorphicOn`, `BHW.extendF_complex_lorentz_invariant`, and `DΩ.Ω_sub_extendedTube`. |
| `BHW.OS45BHWJostLocalContinuationData` and `BHW.os45_BHWJostLocalContinuationData_from_OSI45` | Split required by the route-cycle correction; production Lean not started. | The upstream BHW/Jost hull and branch-continuation pieces may feed `BHW.OS45SourcePatchBHWJostPairData`: `os45_BHWJostHullData_of_figure24`, `os45_BHWJostBranch_onLocalHull_of_OSI45`, the ordinary and selected adjacent branch continuations, holomorphy, complex-Lorentz invariance, and the Wick/real trace formulas from OS I equations (4.1), (4.12), and (4.14).  The full local-continuation data package, including `os45_BHWJostRealBoundaryEq_of_OSI45`, `os45_BHWJostLiftTransport_onSupport_of_OSI45`, and `os45_BHWJostLiftPairing_of_OSI45`, is downstream of the direct source-patch compact theorem and may consume it later.  No source scalar representative, PET independence, EOW envelope, `bvt_W`, final locality, or oriented common-boundary envelope. |
| `BHW.OS45Figure24AdjacentBranchData` and `BHW.os45Figure24_adjacentBranchData_of_OSI45` | Assembly transcript pinned once the local continuation carrier above is supplied; production Lean not started. | OS I §4.5 equations (4.1), (4.12), (4.14), compact zero-diagonal Euclidean symmetry, and BHW continuation of the adjacent branch, split through `OS45AdjacentPermutedTubeBoundaryFunctional`, `OS45AdjacentPermutedTubeLorentzInvariantBranch`, `os45Figure24_adjacentBHWContinuation_to_JostDomain`, the continuation-data producer `os45_bhwJostContinuation_adjacentPermutedBranch`, the assembly theorem `os45_BHWJost_continue_adjacentBranch_from_OSI45`, and the lower carrier theorem `os45_BHWJostLocalContinuationData_from_OSI45`.  The data must carry `adjacent_realBoundary_eq_ordinary` for every compact test supported in `hChart.V0`; this is source content consumed by generic Jost/Ruelle uniqueness, not a consequence of the final lift pairing. |
| `BHW.os45Figure24_realBoundaryEq_of_OSI45` | Mechanical extraction from adjacent branch provenance; production Lean not started. | Rewrite `Dord.ordinaryBranch` by `Dord.ordinaryBranch_def` and use `Dadj.adjacent_realBoundary_eq_ordinary`.  The source proof is in the adjacent BHW/Jost continuation packet; no scalar representative, local source equality, separate source-branch `= OS.S`, PET independence, or final locality. |
| `BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45` | Active route corrected; algebraic `OS45SourcePatchBHWJostPairData` consumer layer checked, analytic OS-I/BHW-Jost producer still open. | Direct OS I §4.5 / BHW-Jost compact producer.  Preferred target: construct `P : OS45SourcePatchBHWJostPairData ... (BHW.os45Figure24SourcePatch ... i hi)` for each adjacent pair.  The checked exact-source-patch consumer `os45CompactFigure24WickPairingEq_of_pairData_on_figure24SourcePatch` derives the compact Wick-pairing packet from that carrier: Euclidean-edge Wick zero, Wick/real-source integrability, `P.difference` identity propagation, and the family/source-anchor packaging are all checked.  A broader carrier on `V` remains acceptable only if it comes with canonical Figure-2-4 source-patch containment.  It must not call `BHW.os45_adjacent_commonBoundaryEnvelope`, `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_id`, `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_adjacent`, the oriented adjacent `S'_n` seed/path package, PET independence, final locality, or the later OS-specific `JostRuelleCompactBoundaryData` package that consumes this compact theorem.  The old common-boundary-envelope transcript was circular and is retained only as rejected archival material. |
| `BHW.os45CommonBoundary_wickTrace_zero_of_compactPairing_zero` and `BHW.os45CommonBoundary_identity_of_wickTrace_zero` | Proof transcript pinned; production Lean not started. | Genuine analytic extraction from the common-boundary envelope: universal compact Wick branch-difference vanishing gives pointwise zero on the Wick trace, then holomorphic identity on the connected common chart. The proof transcript now includes the integrability/bookkeeping helpers `BHW.integrable_pairings_of_os45_adjacent_euclideanEdge_on_timeSector`, `BHW.integral_wickBranchDifference_mul_eq_zero_of_pairing_eq`, and `BHW.integral_commonBoundary_wickTrace_eq_zero_of_wickDiff_zero`, plus the complex-linear Wick-time map `BHW.os45WickRotateCLE` and chart lemma `BHW.os45CommonChartCLE_wickRotateRealConfig_eq`. |
| `BHW.os45CanonicalAdjacentBranchBoundaryData_of_OSI45` | Assembly transcript pinned; production Lean not started. | Field-by-field construction of `JostRuelleCompactBoundaryData`, `jr_lift_eq`, ordinary lift equality on the deterministic lift, and adjacent lift pairing `= OS.S n ψZ`, after the domain, ordinary-branch, adjacent-branch, and real-boundary packets above. It no longer carries individual source-to-Schwinger or lift-to-source PET-overlap fields. |
| `BHW.jostRuelle_uniqueContinuation_compactBoundary` | OS-free analytic theorem; transcript pinned; production Lean not started. | `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`, `BHW.identity_theorem_totally_real_product`, support restriction via `tsupport`, and no OS/theorem-2 inputs. |

The ledger is intentionally asymmetric.  The checked Euclidean edge theorem
proves only the compact Wick/Schwinger equality on the real ordered edge; it
does not create the adjacent analytic branch, the connected Jost/Ruelle
domain, or the common real-boundary distribution.  Conversely, the ordinary
branch packet is nearly mechanical once the domain packet exists, but it
cannot be used to bypass the OS-I adjacent branch producer.

Route-cycle correction, 2026-05-03: the previous common-boundary-envelope
transcript for
`BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45` is
rejected.  It put
`BHW.os45_adjacent_commonBoundaryEnvelope` upstream of the compact source-patch
theorem, while the envelope itself is downstream of the oriented adjacent
`S'_n` seed/path package fed by that compact theorem.  The strict DAG is:

```text
direct OS-I §4.5/BHW-Jost source-patch compact theorem
  -> OS45SourcePatchBHWJostPairData
  -> distributional zero of P.difference on the source patch
  -> OS45CompactFigure24WickPairingEq_of_pairData_difference_zero
  -> sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero
  -> os45AdjacentSPrimeOrientedRealSeed_of_compactWickPairingEq
  -> os45AdjacentSPrimeOrientedSourceEq_of_realSeed
  -> os45AdjacentSPrimeOrientedSeedFigure24Path_of_compactWickPairingEq
  -> os45OneBranchOrientedSourceEq_sourceInput_id/adjacent
  -> os45BranchHorizontalOrientedSourceGermAt_of_figure24_id/adjacent
  -> os45_adjacent_commonBoundaryEnvelope
  -> later common-boundary extraction/gluing consumers
```

The direct compact theorem is the OS I §4.5 branch-difference producer: use
the checked compact Wick equality on the zero-diagonal Figure-2-4 edge,
transport it through the OS I equations and BHW continuation to the selected
adjacent Jost/Ruelle real boundary, then read the ordinary `extendF` and
permuted `extendF` real traces on the source patch.  It may not consume
`os45_adjacent_commonBoundaryEnvelope`, the oriented branch-germ suppliers,
the oriented seed/path package, global PET independence, final locality,
`os45_BHWJostRealBoundaryEq_of_OSI45`, or the later OS-specific
`JostRuelleCompactBoundaryData` package that consumes the compact
source-patch theorem.  Any proof transcript using those names is an archived
circular transcript, not Lean-portable active documentation.

Direct OS-I compact producer obligations, Lean-facing form:

Paper anchors for this block are fixed.  In the local OCR of
`references/Reconstruction theorem I.pdf`, OS I §4.5 says that Euclidean
symmetry plus equations `(4.1)`, `(4.12)`, and `(4.14)` give a single-valued,
symmetric analytic continuation on the permuted tube family `S'_n`; only then
does the paragraph invoke Bargmann-Hall-Wightman to enlarge to `S''_n`, and
only after that invoke Jost p. 83 for boundary locality.  In the local OCR of
Hall-Wightman, Theorem I and Lemma I are exactly the Lorentz-invariant
holomorphic-tube theorem: real orthochronous Lorentz invariance promotes to
proper complex-Lorentz invariance and a single-valued continuation to the
extended tube.  Therefore this compact producer may use the OS-I equations,
the checked compact Wick equality, and the proper-complex BHW continuation
machinery, but not the later locality theorem, the downstream oriented
common-boundary envelope, or any theorem that already assumes locality.

1. Wick compact zero.  The compact distributional zero for the branch
   difference on the selected chart is now checked as the Euclidean-edge
   bridge below.  Its Wick integrability inputs are also checked, and the
   canonical Figure-2-4 specialization
   `BHW.integrable_wickEdge_bvt_F_mul_schwartz_on_figure24SourcePatch`
   supplies them on the final source patch.

   ```lean
   theorem BHW.os45_wickBranchDifference_zero_of_euclideanEdge_pairing_eq_on_timeSector
       [NeZero d]
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
       (V : Set (NPointDomain d n))
       (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
       (ρ : Equiv.Perm (Fin n))
       (hV_ordered :
         ∀ x ∈ V,
           x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
       (hV_swap_ordered :
         ∀ x ∈ V,
           (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
             EuclideanOrderedPositiveTimeSector (d := d) (n := n)
               ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
       (hτ_int :
         ∀ χ : SchwartzNPoint d n,
           HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
           tsupport (χ : NPointDomain d n -> ℂ) ⊆ V ->
           Integrable
             (fun x : NPointDomain d n =>
               bvt_F OS lgc n
                 (fun k => wickRotatePoint
                   (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * χ x))
       (hid_int :
         ∀ χ : SchwartzNPoint d n,
           HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
           tsupport (χ : NPointDomain d n -> ℂ) ⊆ V ->
           Integrable
             (fun x : NPointDomain d n =>
               bvt_F OS lgc n
                 (fun k => wickRotatePoint (x k)) * χ x)) :
       ∀ χ : SchwartzNPoint d n,
         HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
         tsupport (χ : NPointDomain d n -> ℂ) ⊆ V ->
         ∫ x : NPointDomain d n,
             (bvt_F OS lgc n
                 (fun k => wickRotatePoint
                   (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
               bvt_F OS lgc n (fun k => wickRotatePoint (x k))) * χ x = 0
   ```

   This theorem uses only `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`
   and the checked integrability/bookkeeping lemma
   `BHW.integral_wickBranchDifference_mul_eq_zero_of_pairing_eq`; it does not
   use BHW continuation, `extendF`, or locality.

2. Direct BHW/Jost difference carrier.  Introduce the direct OS-I compact
   carrier below the public source-patch theorem.  Its role is to store one
   holomorphic branch-difference function whose Wick trace is the Wick
   difference from item 1 and whose real trace is the source `extendF`
   difference.  It is not the local oriented common-boundary envelope: its
   construction comes only from the OS-I equations, BHW continuation on the
   selected Figure-2-4 hull, and the direct source-patch geometry.

   To avoid hiding the analytic construction of `H`, first prove the
   test-independent pair carrier:

   ```lean
   structure BHW.OS45SourcePatchBHWJostPairData
       [NeZero d] (hd : 2 <= d)
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
       (V : Set (NPointDomain d n)) where
     τ : Equiv.Perm (Fin n)
     τ_eq : τ = Equiv.swap i ⟨i.val + 1, hi⟩
     U : Set (Fin n -> Fin (d + 1) -> ℂ)
     V_open : IsOpen V
     V_nonempty : V.Nonempty
     U_open : IsOpen U
     U_connected : IsConnected U
     wick_mem :
       ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U
     real_mem :
       ∀ x ∈ V, BHW.realEmbed x ∈ U
     Bord Btau : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ
     Bord_holo : DifferentiableOn ℂ Bord U
     Btau_holo : DifferentiableOn ℂ Btau U
     Bord_wick_trace :
       ∀ x ∈ V,
         Bord (fun k => wickRotatePoint (x k)) =
           bvt_F OS lgc n (fun k => wickRotatePoint (x k))
     Btau_wick_trace :
       ∀ x ∈ V,
         Btau (fun k => wickRotatePoint (x k)) =
           bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k)))
     Bord_real_trace :
       ∀ x ∈ V,
         Bord (BHW.realEmbed x) =
           BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
     Btau_real_trace :
       ∀ x ∈ V,
         Btau (BHW.realEmbed x) =
           BHW.extendF (bvt_F OS lgc n)
             (BHW.realEmbed (fun k => x (τ k)))
   ```

   `Bord` is the ordinary BHW/Jost branch and `Btau` is the adjacent continued
   branch, both on the same selected Figure-2-4 hull `U`.  The Wick trace
   fields are the OS-I `(4.1)/(4.12)` ordered-sector formulas, with the
   adjacent label normalized by `τ_eq`; the real trace fields are the
   deterministic source-patch boundary identifications for the two branches.
   These trace formulas are source content of OS I §4.5/BHW-Jost, not
   consequences of final locality and not consequences of the oriented
   common-boundary envelope.

   The pair-data producer is the actual hard direct OS-I theorem below this
   public compact surface:

   ```lean
   theorem BHW.os45_sourcePatch_bhwJostPairData_on_figure24SourcePatch_of_OSI45
       [NeZero d] (hd : 2 <= d)
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n) :
       BHW.OS45SourcePatchBHWJostPairData hd OS lgc n i hi
         (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)
   ```

   Proof transcript for the pair-data producer:
   - set `τ := Equiv.swap i ⟨i.val + 1, hi⟩`;
   - set `Pcan := BHW.os45_adjacent_identity_canonicalSourcePatch hd i hi`,
     rewrite its `V` by `BHW.os45Figure24SourcePatch`, and use the checked
     accessors
     `BHW.isOpen_os45Figure24SourcePatch`,
     `BHW.nonempty_os45Figure24SourcePatch`,
     `BHW.os45Figure24SourcePatch_jost`,
     `BHW.os45Figure24SourcePatch_realEmbed_mem_extendedTube`,
     `BHW.os45Figure24SourcePatch_swapRealEmbed_mem_extendedTube`,
     `BHW.permAct_realEmbed`,
     `BHW.os45Figure24SourcePatch_ordered`, and
     `BHW.os45Figure24SourcePatch_swap_ordered`;
   - construct the selected BHW/Jost hull `U` as the connected component of
     the local proper-complex Lorentz ambient containing the identity Wick
     edge, the adjacent Wick edge, and the real source patch;
   - build `Bord` by continuing the ordinary `extendF (bvt_F OS lgc n)`
     branch from the identity ordered tube through that hull;
   - build `Btau` by continuing the adjacent permuted branch
     `z ↦ extendF (bvt_F OS lgc n) (fun k => z (τ k))` from the adjacent
     ordered/permuted tube through the same hull;
   - prove both holomorphy fields from BHW continuation on the selected hull;
   - prove the Wick trace formulas by the OS-I equations `(4.1)` and `(4.12)`
     plus `bvt_euclidean_restriction` on the checked zero-diagonal ordered
     edge;
   - prove the real trace formulas by the deterministic Figure-2-4 source
     boundary identification and the checked exact source-patch sector fields.

   A broader chart-local theorem may be added later only as a restriction
   corollary from this exact-source-patch carrier plus
   `BHW.OS45SourcePatchBHWJostPairData.restrict`; it is not the first Lean
   target and must not reintroduce the old `OS45Figure24SourceChartAt` wrapper
   as an analytic dependency.

   The pair-data producer is Lean-ready only after the following lower
   surfaces are implemented.  These are the actual mathematical contents of
   the seven bullets above; the public pair-data theorem must be an assembly
   theorem over them, not the first production `sorry`.

   ```lean
   def BHW.os45SourcePatchBHWJostAmbient
       (d n : Nat) (τ : Equiv.Perm (Fin n)) :
       Set (Fin n -> Fin (d + 1) -> ℂ) :=
     BHW.ExtendedTube d n ∪
       {z | BHW.permAct (d := d) τ z ∈ BHW.ExtendedTube d n}

   def BHW.os45SourcePatchBHWJostHull
       (d n : Nat) (τ : Equiv.Perm (Fin n))
       (z0 : Fin n -> Fin (d + 1) -> ℂ) :
       Set (Fin n -> Fin (d + 1) -> ℂ) :=
     pathComponentIn (BHW.os45SourcePatchBHWJostAmbient d n τ) z0

   structure BHW.OS45SourcePatchBHWJostHullData
       [NeZero d] (hd : 2 <= d)
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
       (V : Set (NPointDomain d n))
       where
     τ : Equiv.Perm (Fin n)
     τ_eq : τ = Equiv.swap i ⟨i.val + 1, hi⟩
     x0 : NPointDomain d n
     x0_mem : x0 ∈ V
     z0 : Fin n -> Fin (d + 1) -> ℂ
     z0_eq : z0 = fun k => wickRotatePoint (x0 k)
     U : Set (Fin n -> Fin (d + 1) -> ℂ)
     U_eq : U = BHW.os45SourcePatchBHWJostHull d n τ z0
     V_open : IsOpen V
     V_nonempty : V.Nonempty
     U_open : IsOpen U
     U_connected : IsConnected U
     wick_id_mem :
       ∀ x, x ∈ V -> (fun k => wickRotatePoint (x k)) ∈ U
     real_id_mem :
       ∀ x, x ∈ V -> BHW.realEmbed x ∈ U
     wick_id_ET :
       ∀ x, x ∈ V ->
         (fun k => wickRotatePoint (x k)) ∈ BHW.ExtendedTube d n
     real_id_ET :
       ∀ x, x ∈ V -> BHW.realEmbed x ∈ BHW.ExtendedTube d n
     real_tau_ET :
       ∀ x, x ∈ V ->
         BHW.permAct (d := d) τ (BHW.realEmbed x) ∈
           BHW.ExtendedTube d n
   ```

   `BHW.isOpen_os45SourcePatchBHWJostAmbient` is proved by
   `BHW.isOpen_extendedTube`, continuity of `BHW.permAct`, and `IsOpen.union`.
   The checked noncomputable constructor
   `BHW.os45_sourcePatch_bhwJostHullData_on_figure24SourcePatch` sets `U` to
   the displayed path component based at a selected source-patch Wick seed.
   `U_open` is now the checked theorem
   `BHW.os45SourcePatchBHWJostHull_open`, whose local topological input is
   `BHW.isOpen_pathComponentIn_of_isOpen_normed`; `U_connected` is
   path-connectedness of the component.  The two `U` membership fields are no
   longer separate Figure-2-4 path/lift obligations: after the selected seed
   gives `z0 ∈ BHW.ExtendedTube d n`, the checked
   `BHW.mem_os45SourcePatchBHWJostHull_of_extendedTube` puts every ordinary
   extended-tube point into the selected hull.  Thus `wick_id_mem` follows from
   `wick_id_ET`, and `real_id_mem` follows from `real_id_ET`.
   `wick_id_ET` comes from the ordered
   sector on the exact source patch and the checked
   `BHW.os45Figure24SourcePatch_wick_mem_extendedTube`.  There is
   deliberately no direct `wick_tau_ET` field: the checked swapped ordered
   sector says the relabelled configuration belongs to its own adjacent
   sector, and it does not by itself prove
   `BHW.permAct τ (fun k => wickRotatePoint (x k)) ∈ BHW.ExtendedTube d n`.
   The adjacent Wick trace is therefore an OS-I/BHW continuation output, not a
   source-patch tube-membership accessor.
   `real_id_ET` is the checked ordinary real source-patch extended-tube
   field, and `real_tau_ET` rewrites by the checked
   `BHW.permAct_realEmbed` before using the swapped real source-patch
   extended-tube field.  The exact topology API to pin in Lean is
   `JoinedIn.mono`, `BHW.isOpen_pathComponentIn_of_isOpen_normed`,
   `BHW.os45SourcePatchBHWJostHull_open`,
   `BHW.mem_os45SourcePatchBHWJostHull_of_extendedTube`,
   and `IsOpen.isConnected_iff_isPathConnected`.  No source
   scalar representative, EOW envelope, PET independence, or final locality is
   allowed in this hull theorem.

   The branch continuation theorem used by the two branch producers must not
   be stated as "an arbitrary holomorphic function on an open subset meeting
   a connected hull extends to the hull."  That statement is false even in
   one complex variable.  The BHW/Jost content is instead the construction of
   a continuation atlas: local holomorphic branches covering the selected
   hull, all compatible on overlaps and agreeing with the starting branch on
   the starting sector.  The Lean-facing carrier is:

   ```lean
   structure BHW.BHWSourcePatchContinuationAtlas
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) where
     chart : Type
     carrier : chart -> Set (Fin n -> Fin (d + 1) -> ℂ)
     branch : chart -> (Fin n -> Fin (d + 1) -> ℂ) -> ℂ
     cover : ∀ z, z ∈ U -> ∃ a, z ∈ carrier a
     carrier_open : ∀ a, IsOpen (carrier a)
     carrier_sub_U : ∀ a, carrier a ⊆ U
     branch_holo : ∀ a, DifferentiableOn ℂ (branch a) (carrier a)
     overlap_eq :
       ∀ a b, Set.EqOn (branch a) (branch b) (carrier a ∩ carrier b)
     base_agree :
       ∀ z, z ∈ Ω0 ∩ U ->
         ∃ a, z ∈ carrier a ∧ branch a z = B0 z

   theorem BHW.bhw_sourcePatchHull_has_continuationAtlas
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hΩ0_sub_ambient :
         Ω0 ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (hU_hull :
         ∃ z0, U = BHW.os45SourcePatchBHWJostHull d n τ z0)
       (hΩ0_meets_U : (Ω0 ∩ U).Nonempty)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z) :
       BHW.BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0

   theorem BHW.bhw_glue_sourcePatchContinuationAtlas
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (A : BHW.BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0) :
       ∃ B : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ,
         DifferentiableOn ℂ B U ∧
         (∀ z, z ∈ Ω0 -> z ∈ U -> B z = B0 z)

   theorem BHW.bargmannHallWightman_continue_branch_on_sourcePatchHull
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hΩ0_sub_ambient :
         Ω0 ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (hU_hull :
         ∃ z0, U = BHW.os45SourcePatchBHWJostHull d n τ z0)
       (hΩ0_meets_U : (Ω0 ∩ U).Nonempty)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z) :
       ∃ B : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ,
         DifferentiableOn ℂ B U ∧
         (∀ z, z ∈ Ω0 -> z ∈ U -> B z = B0 z)
   ```

   `bhw_glue_sourcePatchContinuationAtlas` is now checked.  It defines `B z`
   by choosing a chart containing `z`, uses `A.overlap_eq` for independence of
   the chart choice, proves holomorphy locally from `A.branch_holo`, and proves
   agreement with `B0` from `A.base_agree`.  The hard theorem is
   `bhw_sourcePatchHull_has_continuationAtlas`.  It is precisely the local
   Bargmann-Hall-Wightman/Jost theorem: real orthochronous Lorentz invariance
   gives local constancy in proper-complex Lorentz exponential charts; finite
   continuation chains in the displayed hull give local branches; and the
   closed invariant-monodromy theorem gives overlap equality and
   single-valuedness.  It is allowed to use the Hall-Wightman Lemma-1 proof
   and OS I `(4.14)` covariance
   input for `bvt_F`; it is not allowed to call global PET branch
   independence, `fullExtendF`, global source-representative packages, or
   locality.

   The atlas producer itself must be implemented through local invariant
   continuation charts, not by postulating an atlas.  These charts are local
   Hall-Wightman/Jost proof objects; in the conditional ordinary fork they use
   scalar-product descent, while in the strict route they use oriented-source
   descent.  In either case they must not consume the global
   `SourceScalarRepresentativeData` package as an input.  Each chart carrier
   and scalar/oriented germ domain is explicitly preconnected: the identity
   theorem only propagates branch equality across the active component, so
   every Hall-Wightman/Jost neighborhood must be shrunk to an open
   preconnected carrier and a preconnected invariant-domain patch before it
   is stored in a local chart or continuation chain.

   Critical route gate: the following plain-Gram `BHWJostLocalScalar...`
   packet is a conditional ordinary fork, not yet the strict OS I §4.5
   production target.  Its field `branch_same_sourceGram` is mathematically
   available only from the full-component Hall-Wightman source theorem
   discussed in the paper-source audit.  If the proof stays on the strict
   proper-complex route, every occurrence of `sourceMinkowskiGram`,
   `SourceVarietyGermHolomorphicOn`, and
   `IsRelOpenInSourceComplexGramVariety` in this packet must be replaced by
   the oriented invariant API:

   ```lean
   structure BHW.BHWJostLocalOrientedContinuationChart
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ)) where
     carrier : Set (Fin n -> Fin (d + 1) -> ℂ)
     carrier_open : IsOpen carrier
     carrier_preconnected : IsPreconnected carrier
     carrier_sub_U : carrier ⊆ U
     orientedDomain : Set (BHW.SourceOrientedGramData d n)
     oriented_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n orientedDomain
     oriented_preconnected : IsPreconnected orientedDomain
     oriented_sub_variety :
       orientedDomain ⊆ BHW.sourceOrientedGramVariety d n
     oriented_mem :
       ∀ z, z ∈ carrier ->
         BHW.sourceOrientedMinkowskiInvariant d n z ∈ orientedDomain
     oriented_realizes :
       ∀ G, G ∈ orientedDomain ->
         ∃ z, z ∈ carrier ∧
           BHW.sourceOrientedMinkowskiInvariant d n z = G
     Psi : BHW.SourceOrientedGramData d n -> ℂ
     Psi_holo :
       BHW.SourceOrientedVarietyGermHolomorphicOn d n Psi orientedDomain
     branch : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ
     branch_eq_orientedPullback :
       ∀ z, z ∈ carrier ->
         branch z =
           Psi (BHW.sourceOrientedMinkowskiInvariant d n z)
     branch_holo : DifferentiableOn ℂ branch carrier
     branch_same_sourceOrientedInvariant :
       ∀ z w, z ∈ carrier -> w ∈ carrier ->
         BHW.sourceOrientedMinkowskiInvariant d n z =
           BHW.sourceOrientedMinkowskiInvariant d n w ->
         branch z = branch w
     branch_complexLorentzInvariant :
       ∀ Λ z, z ∈ carrier ->
         BHW.complexLorentzAction Λ z ∈ carrier ->
           branch (BHW.complexLorentzAction Λ z) = branch z

   structure BHW.BHWJostOrientedTransitionData
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (Cleft Cright :
         BHW.BHWJostLocalOrientedContinuationChart hd n τ U)
       (p q : Fin n -> Fin (d + 1) -> ℂ) where
     sourcePatch : Set (Fin n -> Fin (d + 1) -> ℂ)
     sourcePatch_open : IsOpen sourcePatch
     sourcePatch_preconnected : IsPreconnected sourcePatch
     sourcePatch_nonempty : sourcePatch.Nonempty
     source_mem : p ∈ sourcePatch
     target_mem : q ∈ Cright.carrier
     sourcePatch_sub :
       sourcePatch ⊆ Cleft.carrier ∩ Cright.carrier
     source_branch_agree :
       Set.EqOn Cleft.branch Cright.branch sourcePatch
     orientedPatch : Set (BHW.SourceOrientedGramData d n)
     orientedPatch_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n orientedPatch
     orientedPatch_preconnected : IsPreconnected orientedPatch
     orientedPatch_nonempty : orientedPatch.Nonempty
     orientedPatch_sub :
       orientedPatch ⊆ Cleft.orientedDomain ∩ Cright.orientedDomain
     sourcePatch_oriented_mem :
       ∀ y, y ∈ sourcePatch ->
         BHW.sourceOrientedMinkowskiInvariant d n y ∈ orientedPatch
     orientedPatch_source_realizes :
       ∀ G, G ∈ orientedPatch ->
         ∃ y, y ∈ sourcePatch ∧
           BHW.sourceOrientedMinkowskiInvariant d n y = G
     oriented_psi_agree :
       Set.EqOn Cleft.Psi Cright.Psi orientedPatch
   ```

   The strict-route local producers are the oriented replacements for the
   plain-Gram one-step packet.  They have the same topology shape as the
   conditional ordinary fork, but the seed descends through
   `sourceOrientedMinkowskiInvariant` and `Psi`.

   ```lean
   theorem BHW.bhw_jost_initialOrientedContinuationChart_at
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hΩ0_sub_ambient :
         Ω0 ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p : Fin n -> Fin (d + 1) -> ℂ}
       (hp : p ∈ Ω0 ∩ U) :
       ∃ C : BHW.BHWJostLocalOrientedContinuationChart hd n τ U,
       ∃ P : Set (Fin n -> Fin (d + 1) -> ℂ),
         p ∈ P ∧
         IsOpen P ∧ IsPreconnected P ∧ P.Nonempty ∧
         P ⊆ Ω0 ∩ C.carrier ∧
         Set.EqOn C.branch B0 P

   theorem BHW.bhw_jost_localOrientedDescent_from_chartBranch_star
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hU_open : IsOpen U)
       (hU_sub_ambient :
         U ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (Cprev : BHW.BHWJostLocalOrientedContinuationChart hd n τ U)
       {p : Fin n -> Fin (d + 1) -> ℂ}
       (hpC : p ∈ Cprev.carrier)
       (hpU : p ∈ U) :
       ∃ N ∈ 𝓝 p, IsOpen N ∧ p ∈ N ∧
         ∀ q, q ∈ N -> q ∈ U ->
           Nonempty
             (Σ Cnext : BHW.BHWJostLocalOrientedContinuationChart hd n τ U,
               BHW.BHWJostOrientedTransitionData hd n τ U Cprev Cnext p q)

   structure BHW.BHWJostOrientedSourceNormalFormGeometryPatch
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (center : Fin n -> Fin (d + 1) -> ℂ) where
     carrier : Set (Fin n -> Fin (d + 1) -> ℂ)
     carrier_open : IsOpen carrier
     carrier_preconnected : IsPreconnected carrier
     center_mem : center ∈ carrier
     carrier_sub_U : carrier ⊆ U
     orientedDomain : Set (BHW.SourceOrientedGramData d n)
     oriented_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n orientedDomain
     oriented_preconnected : IsPreconnected orientedDomain
     oriented_sub_variety :
       orientedDomain ⊆ BHW.sourceOrientedGramVariety d n
     oriented_mem :
       ∀ z, z ∈ carrier ->
         BHW.sourceOrientedMinkowskiInvariant d n z ∈ orientedDomain
     oriented_realizes :
       ∀ G, G ∈ orientedDomain ->
         ∃ z, z ∈ carrier ∧
           BHW.sourceOrientedMinkowskiInvariant d n z = G

   noncomputable def BHW.bhw_jost_orientedSourceNormalFormGeometryPatch_at
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hU_open : IsOpen U)
       (hU_sub_ambient :
         U ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       {center : Fin n -> Fin (d + 1) -> ℂ}
       (hcenter : center ∈ U) :
       BHW.BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center

   theorem BHW.bhw_jost_uniformOrientedDescent_on_sourceNormalFormPatch
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       {center : Fin n -> Fin (d + 1) -> ℂ}
       (G : BHW.BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center)
       (Cprev : BHW.BHWJostLocalOrientedContinuationChart hd n τ U)
       {p q : Fin n -> Fin (d + 1) -> ℂ}
       (hpG : p ∈ G.carrier)
       (hqG : q ∈ G.carrier)
       (hpC : p ∈ Cprev.carrier) :
       Nonempty
         (Σ Cnext : BHW.BHWJostLocalOrientedContinuationChart hd n τ U,
           BHW.BHWJostOrientedTransitionData hd n τ U Cprev Cnext p q)

   structure BHW.BHWJostOrientedBranchFreeTransferNeighborhood
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (center : Fin n -> Fin (d + 1) -> ℂ) where
     N : Set (Fin n -> Fin (d + 1) -> ℂ)
     N_mem_nhds : N ∈ 𝓝 center
     N_open : IsOpen N
     center_mem : center ∈ N
     transfer :
       ∀ p q, p ∈ N -> p ∈ U -> q ∈ N -> q ∈ U ->
       ∀ Cprev : BHW.BHWJostLocalOrientedContinuationChart hd n τ U,
         p ∈ Cprev.carrier ->
           Σ Cnext : BHW.BHWJostLocalOrientedContinuationChart hd n τ U,
             BHW.BHWJostOrientedTransitionData hd n τ U Cprev Cnext p q

   noncomputable def BHW.bhw_jost_orientedBranchFreeTransferNeighborhood_at
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hU_open : IsOpen U)
       (hU_sub_ambient :
         U ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       {p : Fin n -> Fin (d + 1) -> ℂ}
       (hpU : p ∈ U) :
       BHW.BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U p
   ```

   The oriented chain and closed-loop carriers are the field-for-field
   replacements of `BHWSourcePatchContinuationChain` and
   `BHWJostClosedContinuationLoop`, with
   `BHWJostLocalOrientedContinuationChart` replacing local scalar charts,
   `BHWJostOrientedTransitionData` replacing scalar transitions, and
   `closing_orientedPatch` replacing `closing_gramPatch`:

   ```lean
   structure BHW.BHWJostOrientedSourcePatchContinuationChain
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (p0 z : Fin n -> Fin (d + 1) -> ℂ) where
     base_mem : p0 ∈ Ω0 ∩ U
     m : Nat
     node : Fin (m + 1) -> Fin n -> Fin (d + 1) -> ℂ
     node_zero : node 0 = p0
     node_last : node (Fin.last m) = z
     chart : Fin (m + 1) -> Set (Fin n -> Fin (d + 1) -> ℂ)
     node_mem : ∀ j, node j ∈ chart j
     localChart :
       Fin (m + 1) ->
         BHW.BHWJostLocalOrientedContinuationChart hd n τ U
     branch : Fin (m + 1) ->
       (Fin n -> Fin (d + 1) -> ℂ) -> ℂ
     chart_open : ∀ j, IsOpen (chart j)
     chart_preconnected : ∀ j, IsPreconnected (chart j)
     chart_sub_U : ∀ j, chart j ⊆ U
     chart_eq_local : ∀ j, chart j = (localChart j).carrier
     branch_eq_local :
       ∀ j y, y ∈ chart j -> branch j y = (localChart j).branch y
     branch_holo : ∀ j, DifferentiableOn ℂ (branch j) (chart j)
     start_patch : Set (Fin n -> Fin (d + 1) -> ℂ)
     start_patch_open : IsOpen start_patch
     start_patch_preconnected : IsPreconnected start_patch
     start_patch_nonempty : start_patch.Nonempty
     start_mem : p0 ∈ start_patch
     start_patch_sub : start_patch ⊆ Ω0 ∩ chart 0
     start_agree :
       ∀ y, y ∈ start_patch -> branch 0 y = B0 y
     transition_patch :
       ∀ j : Fin m, Set (Fin n -> Fin (d + 1) -> ℂ)
     transition_patch_open : ∀ j, IsOpen (transition_patch j)
     transition_patch_nonempty : ∀ j, (transition_patch j).Nonempty
     transition_patch_preconnected :
       ∀ j, IsPreconnected (transition_patch j)
     transition_patch_sub_left :
       ∀ j, transition_patch j ⊆ chart (Fin.castSucc j)
     transition_patch_sub_right :
       ∀ j, transition_patch j ⊆ chart j.succ
     consecutive_agree :
       ∀ j : Fin m, ∀ y,
         y ∈ transition_patch j ->
           branch (Fin.castSucc j) y = branch j.succ y
     oriented_transition :
       ∀ j : Fin m,
         BHW.BHWJostOrientedTransitionData hd n τ U
           (localChart (Fin.castSucc j)) (localChart j.succ)
           (node (Fin.castSucc j)) (node j.succ)
     final_mem : z ∈ chart (Fin.last m)
     chart_is_lorentz_step :
       ∀ j, ∃ Ωbase : Set (Fin n -> Fin (d + 1) -> ℂ),
         IsOpen Ωbase ∧
         Ωbase ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ ∧
         ∃ Λ : ComplexLorentzGroup d,
           chart j =
             (fun u => BHW.complexLorentzAction Λ u) '' Ωbase

   theorem BHW.BHWJostOrientedSourcePatchContinuationChain.exists_of_nodeSteps
       ... :
       Nonempty
         (BHW.BHWJostOrientedSourcePatchContinuationChain
           hd n τ Ω0 U B0 p0 (node (Fin.last m)))

   noncomputable def BHW.BHWJostOrientedSourcePatchContinuationChain.ofTransferCover
       ... :
       BHW.BHWJostOrientedSourcePatchContinuationChain
         hd n τ Ω0 U B0 p0 (γ 1)

   noncomputable def BHW.bhw_jost_orientedContinuationChain_of_transferCover
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (γ : unitInterval -> Fin n -> Fin (d + 1) -> ℂ)
       (hγ : Continuous γ)
       (hγ_zero : γ 0 = p0)
       (hγU : ∀ t : unitInterval, γ t ∈ U)
       (T :
         ∀ t : unitInterval,
           BHW.BHWJostOrientedBranchFreeTransferNeighborhood
             hd n τ U (γ t))
       (C0 : BHW.BHWJostLocalOrientedContinuationChart hd n τ U)
       (hbase : p0 ∈ Ω0 ∩ U)
       (hp0C : p0 ∈ C0.carrier)
       (start_patch : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hstart_open : IsOpen start_patch)
       (hstart_preconnected : IsPreconnected start_patch)
       (hstart_nonempty : start_patch.Nonempty)
       (hstart_mem : p0 ∈ start_patch)
       (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
       (hstart_agree : ∀ y, y ∈ start_patch -> C0.branch y = B0 y) :
       BHW.BHWJostOrientedSourcePatchContinuationChain
         hd n τ Ω0 U B0 p0 (γ 1)

   noncomputable def
       BHW.bhw_jost_orientedContinuationChainAt_of_pathConnected_transferCover
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (hU_path : IsPathConnected U)
       (T :
         ∀ z, z ∈ U ->
           BHW.BHWJostOrientedBranchFreeTransferNeighborhood hd n τ U z)
       (C0 : BHW.BHWJostLocalOrientedContinuationChart hd n τ U)
       (hbase : p0 ∈ Ω0 ∩ U)
       (hp0C : p0 ∈ C0.carrier)
       (start_patch : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hstart_open : IsOpen start_patch)
       (hstart_preconnected : IsPreconnected start_patch)
       (hstart_nonempty : start_patch.Nonempty)
       (hstart_mem : p0 ∈ start_patch)
       (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
       (hstart_agree : ∀ y, y ∈ start_patch -> C0.branch y = B0 y) :
       ∀ z, z ∈ U ->
         BHW.BHWJostOrientedSourcePatchContinuationChain
           hd n τ Ω0 U B0 p0 z

   noncomputable def BHW.bhw_continuedValueAlongOrientedChain
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       {p0 z : Fin n -> Fin (d + 1) -> ℂ}
       (C :
         BHW.BHWJostOrientedSourcePatchContinuationChain
           hd n τ Ω0 U B0 p0 z) : ℂ :=
     C.branch (Fin.last C.m) z

   structure BHW.BHWJostOrientedClosedContinuationLoop
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (p0 : Fin n -> Fin (d + 1) -> ℂ) where
     chain :
       BHW.BHWJostOrientedSourcePatchContinuationChain
         hd n τ Ω0 U B0 p0 p0
     final_base_mem : p0 ∈ chain.chart (Fin.last chain.m)
     closing_patch : Set (Fin n -> Fin (d + 1) -> ℂ)
     closing_patch_open : IsOpen closing_patch
     closing_patch_preconnected : IsPreconnected closing_patch
     closing_patch_nonempty : closing_patch.Nonempty
     closing_patch_mem : p0 ∈ closing_patch
     closing_patch_sub_start :
       closing_patch ⊆ chain.start_patch
     closing_patch_sub_final :
       closing_patch ⊆ chain.chart (Fin.last chain.m)
     closing_orientedPatch : Set (BHW.SourceOrientedGramData d n)
     closing_orientedPatch_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n closing_orientedPatch
     closing_orientedPatch_preconnected :
       IsPreconnected closing_orientedPatch
     closing_orientedPatch_nonempty : closing_orientedPatch.Nonempty
     closing_orientedPatch_sub_start :
       closing_orientedPatch ⊆ (chain.localChart 0).orientedDomain
     closing_orientedPatch_sub_final :
       closing_orientedPatch ⊆
         (chain.localChart (Fin.last chain.m)).orientedDomain
     closing_patch_oriented_mem :
       ∀ y, y ∈ closing_patch ->
         BHW.sourceOrientedMinkowskiInvariant d n y ∈ closing_orientedPatch

   theorem BHW.bhw_jost_closedChain_orientedMonodromy_trivial
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L :
         BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         L.closing_orientedPatch

   structure BHW.BHWJostOrientedMaxRankClosedLoopSeed
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L :
         BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) where
     seed : Set (BHW.SourceOrientedGramData d n)
     seed_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n seed
     seed_preconnected : IsPreconnected seed
     seed_nonempty : seed.Nonempty
     seed_sub :
       seed ⊆ L.closing_orientedPatch ∩
         {G | BHW.SourceOrientedMaxRankAt d n G}
     seed_eq :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         seed

   theorem BHW.bhw_jost_orientedMaxRankClosedLoopSeed_of_BHW
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L :
         BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Nonempty (BHW.BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L)

   theorem BHW.bhw_jost_closedChain_orientedMaxRankMonodromy_of_seed
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hn : d + 1 <= n)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L :
         BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
       (S :
         BHW.BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         (L.closing_orientedPatch ∩
           {G | BHW.SourceOrientedMaxRankAt d n G})

   theorem BHW.bhw_jost_closedChain_orientedMaxRankMonodromy_trivial
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hn : d + 1 <= n)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L :
         BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         (L.closing_orientedPatch ∩
           {G | BHW.SourceOrientedMaxRankAt d n G})

   theorem BHW.bhw_jost_closedChain_orientedMonodromy_extend_from_maxRank
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hn : d + 1 <= n)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L :
         BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0)
       (hmax :
         Set.EqOn
           (L.chain.localChart (Fin.last L.chain.m)).Psi
           (L.chain.localChart 0).Psi
           (L.closing_orientedPatch ∩
             {G | BHW.SourceOrientedMaxRankAt d n G})) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         L.closing_orientedPatch

   theorem BHW.bhw_jost_closedChain_orientedMonodromy_smallArity
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hn : n < d + 1)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L :
         BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         L.closing_orientedPatch

   theorem BHW.bhw_jost_orientedClosedChain_monodromy_trivial
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L :
         BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Set.EqOn
         (L.chain.branch (Fin.last L.chain.m)) B0 L.closing_patch

   theorem BHW.bhw_jost_terminalOrientedBranches_eq_of_closed_monodromy
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p0 z : Fin n -> Fin (d + 1) -> ℂ}
       (C₁ C₂ :
         BHW.BHWJostOrientedSourcePatchContinuationChain
           hd n τ Ω0 U B0 p0 z) :
       BHW.BHWOrientedTerminalChainComparisonData C₁ C₂

   theorem BHW.bhw_branch_orientedChain_singleValued_on_sourcePatchHull
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hU_hull :
         ∃ z0, U = BHW.os45SourcePatchBHWJostHull d n τ z0)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p0 z : Fin n -> Fin (d + 1) -> ℂ}
       (C₁ C₂ :
         BHW.BHWJostOrientedSourcePatchContinuationChain
           hd n τ Ω0 U B0 p0 z) :
       BHW.bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 C₁ =
         BHW.bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 C₂

   structure BHW.BHWOrientedContinuationChainAtlasData
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) where
     p0 : Fin n -> Fin (d + 1) -> ℂ
     base_mem : p0 ∈ Ω0 ∩ U
     chainAt :
       ∀ z, z ∈ U ->
         BHW.BHWJostOrientedSourcePatchContinuationChain
           hd n τ Ω0 U B0 p0 z
     terminal_overlap_eq :
       ∀ a b : {z // z ∈ U},
         Set.EqOn
           ((chainAt a.1 a.2).branch (Fin.last (chainAt a.1 a.2).m))
           ((chainAt b.1 b.2).branch (Fin.last (chainAt b.1 b.2).m))
           ((chainAt a.1 a.2).chart (Fin.last (chainAt a.1 a.2).m) ∩
             (chainAt b.1 b.2).chart (Fin.last (chainAt b.1 b.2).m))
     terminal_base_agree :
       ∀ z (hz : z ∈ Ω0 ∩ U),
         (chainAt z hz.2).branch
           (Fin.last (chainAt z hz.2).m) z = B0 z
   ```

   Superseded-signature warning for the displayed monodromy block: the
   downstream monodromy names remain intended consumers, but the displayed
   seed-producer surface `bhw_jost_orientedMaxRankClosedLoopSeed_of_BHW`
   hypothesis list is too weak if read as an arbitrary-closed-loop theorem.
   Its hard-range proof must
   first obtain source-backed data for the particular loop produced by the
   strict OS I §4.5 BHW/Jost atlas.  On the large-start-domain route that data
   is `BHWJostOrientedClosedLoopFiniteOverlapDomainData`; on the preferred
   patch-by-patch route it is
   `BHWJostOrientedClosingPatchTerminalSeedData`.  It may not consume only
   `hU_open`, `hU_connected`, and an arbitrary
   `BHWJostOrientedClosedContinuationLoop`.  The checked finite-overlap and
   terminal-seed consumers below are the replacement implementation surfaces
   for that seed producer.

   The checked chain surface deliberately has no
   `transition_patch_eq_sourcePatch` field.  The `snoc` constructor stores
   `T.sourcePatch` as the new transition patch, but downstream agreement uses
   only `consecutive_agree`, `transition_patch_sub_left/right`, and
   `branch_eq_local`; this avoids dependent casts without weakening the
   mathematical data.  The finite compactness part is now implemented by
   `exists_of_nodeSteps`, `ofNodeSteps`, `exists_of_subdivision`,
   `ofSubdivision`, `exists_of_transferCover`, and `ofTransferCover`; the
   remaining non-mechanical content is the initial local chart and the
   branch-free one-step Hall-Wightman/Jost transfer producer.

   The chart fields `oriented_realizes` and
   `orientedPatch_source_realizes` are load-bearing.  They are obtained from
   the same source-normal-form patch that constructs the chart: after
   shrinking to the local image of `sourceOrientedMinkowskiInvariant`, every
   invariant in the stored oriented domain has a source representative in the
   stored carrier, and every invariant in a transition patch has a source
   representative in the stored source overlap.  The proof of
   `oriented_psi_agree` is therefore a real source-to-invariant descent:
   choose source representatives in `sourcePatch`, rewrite both branches by
   `branch_eq_orientedPullback`, use `source_branch_agree`, and then use the
   local identity theorem on the preconnected oriented patch.  No equality of
   `Psi` values may be asserted from bare source-image inclusion alone.

   The proof of `bhw_jost_closedChain_orientedMonodromy_trivial` is an arity
   split.  If `n < d + 1`, the oriented determinant coordinates are vacuous,
   and `bhw_jost_closedChain_orientedMonodromy_smallArity` transports the
   checked pure-Gram small-arity identity-principle proof across the oriented
   coordinate equivalence.  In the remaining case, first call one of the
   genuine Hall-Wightman/Jost loop inputs now exposed in Lean: either the
   large-start-domain package
   `BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L`, or, on
   the patch-by-patch route, the accumulated-germ package
   `BHWJostOrientedClosingPatchTerminalSeedData L`.  This theorem is the real
   monodromy content, but it must not be implemented as a global source
   representative shortcut or as a "common seed in every transition patch"
   shortcut.  The checked `of_commonTransitionSeed` constructor is only a
   sufficient degenerate telescope case; for a moving closed chain the common
   intersection of all transition patches need not be nonempty.

   There are two distinct Lean-ready statements of the Hall-Wightman Lemma-1
   argument.  If the source-backed construction really produces a large
   starting oriented domain covering the whole finite-overlap ribbon, it may
   use the checked finite-overlap trace with
   `Φ := (L.chain.localChart 0).Psi` and return
   `BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L`.  This
   route explicitly requires every positive step domain and closing domain to
   lie in `(L.chain.localChart 0).orientedDomain`.

   If the construction is patch-by-patch, the Lean-ready target is instead
   `BHWJostOrientedClosingPatchTerminalSeedData L`.  The hard proof carries
   the continued branch germ through the finite closed path using the current
   local chart at each step, then chooses:
   `sourceSeed`, an actual OS I §4.5 source patch contained in both the
   initial and terminal carriers; and `terminalSeed`, a nonempty relatively
   open max-rank oriented seed with
   `terminalSeed ⊆ L.closing_orientedPatch`.  The source patch must realize
   the oriented seed:
   `∀ G ∈ terminalSeed, ∃ y ∈ sourceSeed,
     sourceOrientedMinkowskiInvariant d n y = G`.
   The genuine Hall-Wightman/Jost closed-path input is then exactly
   `Set.EqOn (L.chain.localChart (Fin.last L.chain.m)).branch
     (L.chain.localChart 0).branch sourceSeed`.
   The checked final package is:
   `BHWJostOrientedClosingPatchTerminalSeedData.of_sourcePatch_eqOn hn
      terminalSeed_relOpen terminalSeed_nonempty terminalSeed_sub_closing
      terminalSeed_sub_max sourceSeed_sub_initial sourceSeed_sub_final
      sourceSeed_realizes hsource_eq`.
   This is the strict OS I §4.5 source-patch transcript.  If the proof is
   phrased pointwise instead, for each `G` in the seed use
   `BHWJostOrientedClosedContinuationLoop.exists_initial_final_source_realizations_of_closing`
   (or its branch-rewrite variant) to obtain source representatives `y0` and
   `yF` in the initial and terminal carriers with oriented invariant `G`.
   The checked constructor
   `BHWJostOrientedClosingPatchTerminalSeedData.of_sourceRealized_branch_eq`
   then rewrites this source-level equality into the required
   terminal/initial `Psi` equality.
   A useful stronger whole-closing-patch target is the
   existential checked constructor
   `BHWJostOrientedClosingPatchTerminalSeedData.of_closingPatch_exists_sourceBranch_eq`:
   for every `G ∈ L.closing_orientedPatch`, produce one initial source
   representative and one terminal source representative with invariant `G`
   and equal branch values.  It performs max-rank seed extraction
   automatically.  If the Hall-Wightman/Jost argument naturally proves the
   stronger universal equality for all matching representatives, the checked
   constructor `of_closingPatch_sourceBranch_eq` is also available.  The
   terminal-seed endpoint consumer is
   `BHW.bhw_jost_closedChain_sourceMonodromy_of_closingPatchTerminalSeedData`,
   while
   `BHW.bhw_jost_closedChain_sourceMonodromy_of_closingPatch_exists_sourceBranch_eq`
   is the direct endpoint from stronger whole-closing-patch existential
   equality.

   The theorem `bhw_jost_closedChain_orientedMaxRankMonodromy_of_seed` is then
   the identity-principle propagation, not the monodromy theorem.  Let
   `H := (L.chain.localChart (Fin.last L.chain.m)).Psi -
     (L.chain.localChart 0).Psi` and let `S` be the seed above.  Restrict both
   `Psi_holo` fields to `L.closing_orientedPatch`, apply
   `SourceOrientedVarietyGermHolomorphicOn.sub`, and call
   `sourceOrientedGramVariety_maxRank_eqOn_of_connected_fullFrame` with
   `U := L.closing_orientedPatch`, `W := S.seed`, and
   `Ureg := L.closing_orientedPatch ∩
     {G | SourceOrientedMaxRankAt d n G}`.  The hypotheses are:
   `L.closing_orientedPatch_relOpen`;
   the explicit connectedness of
   `L.closing_orientedPatch ∩ MaxRank` supplied by the finite-overlap
   source-backed data or by
   `sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected`;
   `S.seed_relOpen`, `S.seed_nonempty`, and `S.seed_sub`; and the zero
   statement from `S.seed_eq` after rewriting subtraction.  The extra
   `W ⊆ MaxRank` hypothesis is exactly `S.seed_sub`'s second projection.
   This gives equality on the whole max-rank part of the closing patch.
   Finally `bhw_jost_closedChain_orientedMaxRankMonodromy_trivial` is a
   consumer assembly: obtain the checked large-start-domain package or the
   checked closing-patch terminal-seed package from the genuine BHW/Jost
   source proof, then call its `to_closedLoopSeed`/monodromy consumer.  The
   old `bhw_jost_orientedMaxRankClosedLoopSeed_of_BHW` name should not be
   implemented as a separate arbitrary-loop theorem.

   `bhw_jost_closedChain_orientedMonodromy_extend_from_maxRank` is then
   mechanical.  Let
   `H := (L.chain.localChart (Fin.last L.chain.m)).Psi -
     (L.chain.localChart 0).Psi` on `L.closing_orientedPatch`.  Build
   `hH_holo` by restricting both `Psi_holo` fields to
   `L.closing_orientedPatch` and applying
   `BHW.SourceOrientedVarietyGermHolomorphicOn.sub`.  The max-rank theorem
   says `Set.EqOn H 0` on
   `L.closing_orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}`.  Apply
   the already audited continuity/density theorem
   `sourceOrientedGramVariety_relOpen_eqOn_zero_of_eqOn_maxRank`, equivalently
   the final extension step inside
   `sourceOrientedGramVariety_identity_principle`, using
   `SourceOrientedVarietyGermHolomorphicOn.continuousOn` and
   `sourceOrientedMaxRank_dense_in_relOpen_inter`.  This yields `H = 0` on
   all of `L.closing_orientedPatch`, which is exactly the main theorem.

   The source-level theorem
   `bhw_jost_orientedClosedChain_monodromy_trivial` is then mechanical.  For
   `y ∈ L.closing_patch`, use `L.closing_patch_oriented_mem` to put
   `G := sourceOrientedMinkowskiInvariant d n y` in
   `L.closing_orientedPatch`.  The oriented monodromy theorem gives equality
   of the final and initial `Psi` values at `G`.  The fields
   `branch_eq_local` and each local chart's `branch_eq_orientedPullback`
   rewrite the final and initial source branches to those two `Psi` values.
   Since `L.closing_patch_sub_start hy` puts `y` in `chain.start_patch`,
   `chain.start_agree y` rewrites the initial source branch to `B0 y`.

   The same-endpoint comparison theorem must be stated with source-backed
   continuation provenance, not as a naive reversal of arbitrary one-sided
   chain data.  The checked transition structure now records
   `target_mem_sourcePatch : q ∈ sourcePatch`, so
   `BHWJostOrientedTransitionData.symm` is a genuine checked reverse of an
   individual overlap.  This is necessary but not sufficient for the terminal
   comparison theorem: after following `C₁` to the common endpoint `z`, there
   is still no free transition from the terminal chart of `C₁` to the terminal
   chart of `C₂`, since that is exactly the equality being proved.

   The Lean-ready surface is therefore a provenance theorem, not an arbitrary
   chain theorem:

   ```lean
   structure BHW.BHWJostOrientedBranchFreeTransferControl
       [NeZero d] (hd : 2 ≤ d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ)) where
     N : Set (Fin n -> Fin (d + 1) -> ℂ)
     N_open : IsOpen N
     transferChart :
       ∀ p q, p ∈ N -> p ∈ U -> q ∈ N -> q ∈ U ->
       ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
         p ∈ Cprev.carrier ->
           BHWJostLocalOrientedContinuationChart hd n τ U
     transferTransition :
       ∀ p q (hpN : p ∈ N) (hpU : p ∈ U)
         (hqN : q ∈ N) (hqU : q ∈ U)
         (Cprev : BHWJostLocalOrientedContinuationChart hd n τ U)
         (hpC : p ∈ Cprev.carrier),
           BHWJostOrientedTransitionData hd n τ U Cprev
             (transferChart p q hpN hpU hqN hqU Cprev hpC) p q

   structure BHW.BHWJostOrientedTransferContinuationTrace
       [NeZero d] (hd : 2 ≤ d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (p0 z : Fin n -> Fin (d + 1) -> ℂ) where
     chain :
       BHWJostOrientedSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z
     -- the actual finite source nodes and the controlling branch-free
     -- transfer controls used to produce each next chart of `chain`
     stepControl :
       (j : Fin chain.m) ->
         BHWJostOrientedBranchFreeTransferControl hd n τ U
     step_left_mem :
       ∀ j, chain.node (Fin.castSucc j) ∈ (stepControl j).N
     step_right_mem :
       ∀ j, chain.node j.succ ∈ (stepControl j).N
     step_transfer_chart_eq :
       ∀ j,
         (stepControl j).transferChart
           (chain.node (Fin.castSucc j)) (chain.node j.succ)
           (step_left_mem j)
           (chain.chart_sub_U (Fin.castSucc j)
             (chain.node_mem (Fin.castSucc j)))
           (step_right_mem j)
           (chain.chart_sub_U j.succ (chain.node_mem j.succ))
           (chain.localChart (Fin.castSucc j))
           (by
             simpa [chain.chart_eq_local (Fin.castSucc j)]
               using chain.node_mem (Fin.castSucc j)) =
           chain.localChart j.succ
   ```

   For atlas overlaps we usually observe a trace at a point in its terminal
   chart rather than at the endpoint originally used to build the trace.  The
   checked carrier is:

   ```lean
   structure BHW.BHWJostOrientedTransferTerminalPointTrace
       [NeZero d] (hd : 2 ≤ d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (p0 y : Fin n -> Fin (d + 1) -> ℂ) where
     endpoint : Fin n -> Fin (d + 1) -> ℂ
     trace :
       BHWJostOrientedTransferContinuationTrace
         hd n τ Ω0 U B0 p0 endpoint
     point_mem : y ∈ trace.chain.chart (Fin.last trace.chain.m)
   ```

   The zero-step and observation constructors are now checked in Lean:

   ```lean
   def BHW.BHWJostOrientedTransferContinuationTrace.base
       (C0 : BHWJostLocalOrientedContinuationChart hd n τ U)
       (hbase : p0 ∈ Ω0 ∩ U)
       (hp0C : p0 ∈ C0.carrier)
       (start_patch : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hstart_open : IsOpen start_patch)
       (hstart_preconnected : IsPreconnected start_patch)
       (hstart_nonempty : start_patch.Nonempty)
       (hstart_mem : p0 ∈ start_patch)
       (hstart_sub : start_patch ⊆ Ω0 ∩ C0.carrier)
       (hstart_agree :
         ∀ y, y ∈ start_patch -> C0.branch y = B0 y) :
       BHWJostOrientedTransferContinuationTrace
         hd n τ Ω0 U B0 p0 p0

   def BHW.BHWJostOrientedTransferTerminalPointTrace.ofTracePoint
       (T :
         BHWJostOrientedTransferContinuationTrace
           hd n τ Ω0 U B0 p0 endpoint)
       (hy : y ∈ T.chain.chart (Fin.last T.chain.m)) :
       BHWJostOrientedTransferTerminalPointTrace
         hd n τ Ω0 U B0 p0 y

   def BHW.BHWJostOrientedTransferTerminalPointTrace.atEndpoint
       (T :
         BHWJostOrientedTransferContinuationTrace
           hd n τ Ω0 U B0 p0 endpoint) :
       BHWJostOrientedTransferTerminalPointTrace
         hd n τ Ω0 U B0 p0 endpoint
   ```

   `base` is the zero-step chain with all transfer-provenance fields over
   `Fin 0`.  The compact-cover construction still uses centered
   `BHWJostOrientedBranchFreeTransferNeighborhood`s to obtain the finite
   subdivision, but after a subdivision interval has selected an actual
   transfer set the trace stores the center-forgotten
   `BHWJostOrientedBranchFreeTransferControl`.  This is the exact data needed
   by the trace induction: membership of the two step endpoints in the
   selected set and equality between the produced `transferChart` and the next
   local chart of the chain.  The helper
   `BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl` performs
   this forgetting, and
   `BHWJostOrientedTransferContinuationTrace.snocAtTerminalNode` appends one
   checked transfer-control step to a trace.  `ofTracePoint` is the exact
   atlas-overlap observation map, and `atEndpoint` is its specialization using
   `T.chain.final_mem`.

   The local output used by the trace induction is the chart-level analogue of
   terminal chain comparison:

   ```lean
   structure BHW.BHWLocalChartTerminalComparisonData
       [NeZero d] {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
       {U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       (Cleft Cright : BHWJostLocalOrientedContinuationChart hd n τ U)
       (q : Fin n -> Fin (d + 1) -> ℂ) where
     terminalPatch : Set (Fin n -> Fin (d + 1) -> ℂ)
     endpoint_mem : q ∈ terminalPatch
     terminalPatch_open : IsOpen terminalPatch
     terminalPatch_preconnected : IsPreconnected terminalPatch
     terminalPatch_sub_left : terminalPatch ⊆ Cleft.carrier
     terminalPatch_sub_right : terminalPatch ⊆ Cright.carrier
     terminal_branches_eq :
       Set.EqOn Cleft.branch Cright.branch terminalPatch
   ```

   The equality step required by this trace is the real one-step
   Hall-Wightman/Jost uniqueness datum for the stored center-forgotten
   transfer control.  The checked Lean interface is now the type-valued
   control property

   ```lean
   def BHW.BHWJostOrientedTransferControlHasUniqueNext
       (K : BHWJostOrientedBranchFreeTransferControl hd n τ U) : Type _ :=
     ∀ {p q : Fin n -> Fin (d + 1) -> ℂ}
       (hpN : p ∈ K.N) (hpU : p ∈ U)
       (hqN : q ∈ K.N) (hqU : q ∈ U)
       {CprevA CprevB :
         BHWJostLocalOrientedContinuationChart hd n τ U}
       (hpA : p ∈ CprevA.carrier) (hpB : p ∈ CprevB.carrier)
       (sourceSeed : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hsourceSeed_mem : p ∈ sourceSeed)
       (hsourceSeed_sub : sourceSeed ⊆ CprevA.carrier ∩ CprevB.carrier)
       (hsourceSeed_eq :
         Set.EqOn CprevA.branch CprevB.branch sourceSeed),
       BHWLocalChartTerminalComparisonData
         (K.transferChart p q hpN hpU hqN hqU CprevA hpA)
         (K.transferChart p q hpN hpU hqN hqU CprevB hpB) q
   ```

   The future local theorem must prove this property for the controls produced
   by source-normal-form Hall-Wightman descent:

   ```lean
   theorem BHW.bhw_jost_orientedTransfer_unique_next
       (K : BHWJostOrientedBranchFreeTransferControl hd n τ U)
       (hK : BHWJostOrientedTransferControlHasUniqueNext K)
       {p q : Fin n -> Fin (d + 1) -> ℂ}
       (hpN : p ∈ K.N) (hpU : p ∈ U)
       (hqN : q ∈ K.N) (hqU : q ∈ U)
       {CprevA CprevB :
         BHWJostLocalOrientedContinuationChart hd n τ U}
       (hpA : p ∈ CprevA.carrier) (hpB : p ∈ CprevB.carrier)
       (sourceSeed : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hsourceSeed_mem : p ∈ sourceSeed)
       (hsourceSeed_sub : sourceSeed ⊆ CprevA.carrier ∩ CprevB.carrier)
       (hsourceSeed_eq :
         Set.EqOn CprevA.branch CprevB.branch sourceSeed) :
       BHWLocalChartTerminalComparisonData
         (K.transferChart p q hpN hpU hqN hqU CprevA hpA)
         (K.transferChart p q hpN hpU hqN hqU CprevB hpB) q
   ```

   Its proof is not a wrapper: it is exactly the local Hall-Wightman descent
   with the previous chart's branch as the seed branch.  It uses
   `branch_same_sourceOrientedInvariant`, `branch_complexLorentzInvariant`,
   and the normal-form source-realization fields to show that two descents
   from equal previous germs give equal next germs on a target source patch
   around `q`.

   The trace-level certified-step predicate is checked as
   `BHWJostOrientedTransferContinuationTrace.HasUniqueSteps Tr`, with the
   zero-step trace certified by
   `BHWJostOrientedTransferContinuationTrace.hasUniqueSteps_base`.  The
   checked bundled carriers are
   `BHWJostOrientedCertifiedTransferContinuationTrace` and
   `BHWJostOrientedCertifiedTransferTerminalPointTrace`; they keep the
   ordinary trace plus the step-uniqueness certificate, and they have
   `base`, `ofTracePoint`, `atEndpoint`, and forgetful maps back to the raw
   terminal-point trace API.  From this one-step uniqueness theorem, prove a
   finite induction
   `bhw_jost_orientedTransferTrace_terminalComparison_of_sameTrace`: two
   certified traces with the same finite nodes and same controlling
   branch-free neighborhoods, and with equal starting germs on an initial
   source patch, have terminal comparison data at the final node.  The
   induction state is a source patch around `chain.node i` contained in both
   current local-chart carriers, with equality of the current branches there;
   the successor case is exactly `bhw_jost_orientedTransfer_unique_next`
   applied to the stored `stepUnique j`.

   Finally the closed-path theorem for two terminal-point traces is:

   ```lean
   theorem BHW.bhw_jost_orientedTerminalPointComparison_of_transferTraces
       (T₁ T₂ :
         BHWJostOrientedCertifiedTransferTerminalPointTrace
           hd n τ Ω0 U B0 p0 y) :
       BHWLocalChartTerminalComparisonData
         (T₁.trace.trace.chain.localChart
           (Fin.last T₁.trace.trace.chain.m))
         (T₂.trace.trace.chain.localChart
           (Fin.last T₂.trace.trace.chain.m)) y
   ```

   The hard proof forms the source closed path obtained by following
   `T₁.trace.trace` and then the reversed source nodes of `T₂.trace.trace`, uses the
   branch-free transfer controls to continue the observed `T₁` terminal germ
   back to a closing patch at `p0`, constructs
   `BHWJostOrientedClosingPatchTerminalSeedData` for that closed loop by the
   strict OS I §4.5 BHW/Jost source-patch argument, and invokes
   `bhw_jost_closedChain_sourceMonodromy_of_closingPatchTerminalSeedData`.
   The resulting equality with `B0` on the closing patch, together with
   equality of the initial chart of the underlying raw trace
   `T₂.trace.trace` with `B0`, is transported forward along the certified
   stored trace of `T₂` by the finite uniqueness induction,
   yielding a terminal patch inside the two observed terminal charts at `y`.  For the
   special case `y = z` with `point_mem := chain.final_mem`, this chart-level
   comparison packages into
   `BHWOrientedTerminalChainComparisonData
   T₁.trace.trace.chain T₂.trace.trace.chain`;
   its checked method `continuedValue_eq` is only the endpoint evaluation.

   The checked assembly target for the atlas-from-chains step is
   `BHWOrientedContinuationChainAtlasData`.  The checked constructor
   `BHWOrientedContinuationChainAtlasData.ofSameEndpointComparisons` remains a
   useful high-level consumer if one has a theorem comparing arbitrary chain
   records, but the strict source-backed route must not try to manufacture
   such a theorem from the current data.  The final strict-route producer should
   instead use the checked certified trace-level variant
   `BHWOrientedContinuationTraceAtlasData.ofCertifiedTerminalPointComparisonsAndInitialChart`
   whose comparison hypothesis ranges over certified terminal-point traces for
   the certified selected transfer traces.  After the trace comparison produces terminal
   branch equality at an overlap point, the atlas forgets the trace provenance
   and stores only the underlying terminal chain chart.  The
   selected-chain field is checked from path-connectedness by
   `BHW.bhw_jost_orientedContinuationChainAt_of_pathConnected_transferCover`:
   use `IsPathConnected.joinedIn p0 hbase.2 z hz`, take
   `JoinedIn.somePath`, and call the compact transfer-cover fold along that
   path.  The selected raw trace field is checked in the same way by
   `BHW.bhw_jost_orientedTransferContinuationTraceAt_of_pathConnected_transferCover`:
   the compact subdivision supplies the centered transfer neighborhoods for
   each adjacent pair, while each stored trace step keeps the center-forgotten
   control actually used by the transfer call.  The selected certified trace
   field is now checked by
   `BHW.bhw_jost_orientedCertifiedTransferContinuationTraceAt_of_pathConnected_transferCover`:
   it runs the same compact-cover fold and stores `HasUniqueSteps` for every
   chosen center-forgotten transfer control.  Consequently the remaining hard
   atlas inputs are the branch-free transfer neighborhoods on `U` together with
   their one-step uniqueness certificates, the certified terminal-point
   comparison theorem for transfer-provenance traces observed at the same
   point, and the initial chart covering `Ω0 ∩ U` with branch `B0`; certified
   trace selection itself is no longer an extra proof obligation.  The
   trace-level constructor derives the atlas
   `terminal_overlap_eq` field directly: for `y` in the intersection of the
   terminal charts of chains ending at `a` and `b`, build terminal-point
   traces from the selected traces for `a` and `b` using the two membership
   proofs, invoke
   `bhw_jost_orientedTerminalPointComparison_of_transferTraces`, and evaluate
   the resulting chart-level branch equality at `y`.

   The checked trace-atlas surface is:

   ```lean
   structure BHW.BHWOrientedContinuationTraceAtlasData
       [NeZero d] (hd : 2 ≤ d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) where
     p0 : Fin n -> Fin (d + 1) -> ℂ
     base_mem : p0 ∈ Ω0 ∩ U
     traceAt :
       ∀ z, z ∈ U ->
         BHWJostOrientedTransferContinuationTrace hd n τ Ω0 U B0 p0 z
     terminal_overlap_comparison :
       ∀ (a b : {z // z ∈ U}) {y : Fin n -> Fin (d + 1) -> ℂ},
         y ∈ (traceAt a.1 a.2).chain.chart
           (Fin.last (traceAt a.1 a.2).chain.m) ->
         y ∈ (traceAt b.1 b.2).chain.chart
           (Fin.last (traceAt b.1 b.2).chain.m) ->
         BHWLocalChartTerminalComparisonData
           ((traceAt a.1 a.2).chain.localChart
             (Fin.last (traceAt a.1 a.2).chain.m))
           ((traceAt b.1 b.2).chain.localChart
             (Fin.last (traceAt b.1 b.2).chain.m)) y
     terminal_base_agree :
       ∀ z (hz : z ∈ Ω0 ∩ U),
         ((traceAt z hz.2).chain.branch
           (Fin.last (traceAt z hz.2).chain.m)) z = B0 z
   ```

   Its checked method
   `BHWOrientedContinuationTraceAtlasData.to_chainAtlasData` proves the
   ordinary atlas overlap field by applying
   `terminal_overlap_comparison a b hya hyb` at an arbitrary overlap point
   `y`, evaluating the returned `BHWLocalChartTerminalComparisonData` at `y`,
   and rewriting both sides by the terminal chains' `branch_eq_local`.  No
   arbitrary same-endpoint chain theorem, and no comparison of arbitrary
   transfer traces, appears in this proof.

   The minimal checked constructor
   `BHWOrientedContinuationTraceAtlasData.ofSelectedComparisonsAndInitialChart`
   takes exactly the two selected comparison inputs needed by the atlas:
   terminal-overlap comparison for the selected traces `traceAt a` and
   `traceAt b`, and base comparison between `traceAt z` and the initial chart
   for `z ∈ Ω0 ∩ U`.

   The certified checked constructor
   `BHWOrientedContinuationTraceAtlasData.ofCertifiedTerminalPointComparisonsAndInitialChart`
   is now the strict-route atlas surface: it forgets certified selected traces
   to raw traces for the stored atlas, derives the selected overlap field by
   observing the certified selected traces as certified terminal-point traces,
   and proves base agreement by comparing the certified selected trace at
   `z ∈ Ω0 ∩ U` with the certified zero-step base trace observed at `z`.
   The older checked constructor
   `BHWOrientedContinuationTraceAtlasData.ofTerminalPointComparisonsAndInitialChart`
   is retained only as a raw-trace convenience wrapper when an unbundled
   terminal-point trace comparison theorem is already available.

   The monodromy-facing bridge is now checked as
   `BHWOrientedTerminalChainComparisonData.ofCertifiedRetargetedTerminalPointTraceComparison`.
   Given two certified terminal-point observations `T₁ T₂` at the same source
   point `y`, the closed-path comparison theorem may first retarget
   `T₁.trace.trace.chain` and `T₂.trace.trace.chain` to endpoint `y` using
   `retargetTerminal Tᵢ.point_mem` and return
   `BHWOrientedTerminalChainComparisonData` for those two same-endpoint
   retargeted chains.  The checked bridge rewrites the final chart and final
   branch of each retargeted chain by
   `BHWJostOrientedSourcePatchContinuationChain.retargetTerminal` and `snoc`,
   producing exactly the `BHWLocalChartTerminalComparisonData` between the
   original terminal local charts.  The raw bridge
   `BHWOrientedTerminalChainComparisonData.ofRetargetedTerminalPointTraceComparison`
   is identical without the stored uniqueness certificates.

   Consequently the checked atlas assembly now has exactly two remaining
   non-mechanical inputs: a source-normal-form/uniform-descent producer of
   branch-free transfer neighborhoods on `U` whose stored controls carry
   `HasUniqueSteps`, and the hard certified retargeted-chain comparison
   theorem for two certified terminal-point observations.  A local
   `bhw_jost_orientedTerminalPointComparison_of_transferTraces` remains a
   valid derived theorem, but it should be proved by the checked retargeted
   bridge after closed-path monodromy has produced the same-endpoint
   comparison data.  The checked
   finite propagation constructor
   `BHW.bhw_jost_orientedTerminalComparison_of_sharedTransferSkeleton`
   handles the case where the two branches have a common finite node/control
   skeleton: base equality on a source seed propagates along all steps by
   reusing each previous terminal comparison patch as the next step's
   `sourceSeed` and applying the stored `HasUniqueNext` theorem.  This is the
   Lean-ready transcript for the repeated one-step uniqueness part of the
   terminal comparison proof.  The remaining non-mechanical work is to obtain,
   from the closed-path/source monodromy construction, either such a shared
   skeleton comparison problem or the retargeted same-endpoint
   `BHWOrientedTerminalChainComparisonData` consumed by the bridge.
   Once a closed-return construction has been reduced to a closed loop against
   the original base chart, the checked
   `BHWJostOrientedClosedContinuationLoop.terminalChainComparison_base_of_closingPatchTerminalSeedData`
   packages closing-patch terminal-seed/source-monodromy data as
   `BHWOrientedTerminalChainComparisonData` between the closed-loop chain and
   the normalized zero-step base chain.  Thus the source-monodromy consumer and
   the chain-comparison consumer now meet at a checked object.
   The checked
   theorem `BHW.bhw_jost_orientedGluedBranch_of_certifiedTraces` composes
   certified selected traces, certified terminal-point comparison, and the
   initial chart to produce the glued holomorphic source-patch branch on `U`.
   The checked path-connected theorem
   `BHW.bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover`
   first selects the certified traces from a path-connected uniqueness-certified
   transfer cover and then applies that certified glue theorem.  The checked
   monodromy-facing theorem
   `BHW.bhw_jost_orientedGluedBranch_of_pathConnected_certifiedTransferCover_retargetedComparisons`
   has the same hypotheses except that the comparison input is already the
   retargeted same-endpoint chain comparison.  The checked
   source-normal-form theorem
   `BHW.bhw_jost_orientedGluedBranch_of_pathConnected_sourceNormalFormProducer`
   specializes this to the source-normal-form patch producer plus uniform
   descent input; after that reduction, the non-mechanical inputs are exactly
   the one-step uniqueness theorem for the produced transfer controls and the
   certified terminal-point comparison theorem.  The newest source-normal-form
   endpoint
   `BHW.bhw_jost_orientedGluedBranch_of_pathConnected_sourceNormalFormProducer_retargetedComparisons`
   is the preferred strict-route target: its final hard comparison hypothesis
   is the closed-path comparison of the two terminal-retargeted certified
   chains, while terminal-chart packaging is entirely mechanical.
   The raw theorem `BHW.bhw_jost_orientedGluedBranch_of_pathConnected_transferCover`
   remains a convenience surface when one has an unbundled terminal-point
   comparison theorem, but the strict route should target the certified
   surface first.

   The variant
   `BHWOrientedContinuationChainAtlasData.ofSameEndpointComparisonsAndBaseChain`
   also derives `terminal_base_agree`: for `z ∈ Ω0 ∩ U`, retarget the
   normalized base chain to endpoint `z`, compare the selected chain ending at
   `z` with that retargeted base chain, and rewrite the retargeted continued
   value back to the stored base-branch equality with `B0`.
   The further specialization
   `BHWOrientedContinuationChainAtlasData.ofSameEndpointComparisonsAndInitialChart`
   builds that normalized base chain as the zero-step chain from the initial
   chart.  Its only additional requirements are the honest initial-chart
   fields `Ω0 ∩ U ⊆ C0.carrier` and
   `∀ z ∈ Ω0 ∩ U, C0.branch z = B0 z`.
   Its method `to_sourcePatchContinuationAtlas` builds the atlas whose charts
   are the terminal source charts and whose branches are the stored terminal
   branches; its method `exists_glued_branch` then calls the checked
   `bhw_glue_sourcePatchContinuationAtlas`.

   The plain-Gram declarations below remain useful only if the full-component
   Hall-Wightman input is supplied.  They are not the active strict OS II /
   OS I §4.5 Lean targets.  On the current route, production Lean must use the
   checked oriented replacements:
   `BHWJostLocalOrientedContinuationChart`,
   `BHWJostOrientedTransitionData`,
   `BHWJostOrientedBranchFreeTransferNeighborhood`,
   `BHWJostOrientedSourcePatchContinuationChain`,
   `BHWJostOrientedClosedContinuationLoop`, and the terminal-seed consumers
   in `SourceOrientedBHWFiniteOverlap.lean`.  In particular,
   `bhw_jost_localContinuationStep` below should not be implemented as a
   scalar theorem on the active route; its oriented replacement is the checked
   branch-free transfer/transition API fed by the source-normal-form producer
   and uniform oriented descent theorem.

   ```lean
   structure BHW.BHWJostLocalScalarContinuationChart
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ)) where
     carrier : Set (Fin n -> Fin (d + 1) -> ℂ)
     carrier_open : IsOpen carrier
     carrier_preconnected : IsPreconnected carrier
     carrier_sub_U : carrier ⊆ U
     gramDomain : Set (Fin n -> Fin n -> ℂ)
     gram_relOpen :
       IsRelOpenInSourceComplexGramVariety d n gramDomain
     gram_preconnected : IsPreconnected gramDomain
     gram_sub_variety :
       gramDomain ⊆ sourceComplexGramVariety d n
     gram_mem :
       ∀ z, z ∈ carrier ->
         BHW.sourceMinkowskiGram d n z ∈ gramDomain
     Phi : (Fin n -> Fin n -> ℂ) -> ℂ
     Phi_holo :
       SourceVarietyGermHolomorphicOn d n Phi gramDomain
     branch : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ
     branch_eq_pullback :
       ∀ z, z ∈ carrier ->
         branch z = Phi (BHW.sourceMinkowskiGram d n z)
     branch_holo : DifferentiableOn ℂ branch carrier
     branch_same_sourceGram :
       ∀ z w, z ∈ carrier -> w ∈ carrier ->
         BHW.sourceMinkowskiGram d n z =
           BHW.sourceMinkowskiGram d n w ->
         branch z = branch w
     branch_complexLorentzInvariant :
       ∀ Λ z, z ∈ carrier ->
         BHW.complexLorentzAction Λ z ∈ carrier ->
           branch (BHW.complexLorentzAction Λ z) = branch z

   theorem BHW.bhw_jost_initialScalarContinuationChart_at
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hΩ0_sub_ambient :
         Ω0 ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p : Fin n -> Fin (d + 1) -> ℂ}
       (hp : p ∈ Ω0 ∩ U) :
       ∃ C : BHW.BHWJostLocalScalarContinuationChart hd n τ U,
       ∃ P : Set (Fin n -> Fin (d + 1) -> ℂ),
         p ∈ P ∧
         IsOpen P ∧ IsPreconnected P ∧ P.Nonempty ∧
         P ⊆ Ω0 ∩ C.carrier ∧
         Set.EqOn C.branch B0 P

   theorem BHW.bhw_jost_localContinuationStep
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hU_open : IsOpen U)
       (hU_sub_ambient :
         U ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (Cprev : BHW.BHWJostLocalScalarContinuationChart hd n τ U)
       {p : Fin n -> Fin (d + 1) -> ℂ}
       (hpC : p ∈ Cprev.carrier) :
       ∃ N ∈ 𝓝 p, ∀ q, q ∈ N -> q ∈ U ->
         ∃ Cnext : BHW.BHWJostLocalScalarContinuationChart hd n τ U,
         ∃ P : Set (Fin n -> Fin (d + 1) -> ℂ),
           p ∈ P ∧ q ∈ Cnext.carrier ∧
           IsOpen P ∧ IsPreconnected P ∧ P.Nonempty ∧
           P ⊆ Cprev.carrier ∩ Cnext.carrier ∧
           Set.EqOn Cprev.branch Cnext.branch P

   theorem BHW.bhw_jost_localDescent_from_chartBranch_star
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hU_open : IsOpen U)
       (hU_sub_ambient :
         U ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (Cprev : BHW.BHWJostLocalScalarContinuationChart hd n τ U)
       {p : Fin n -> Fin (d + 1) -> ℂ}
       (hpC : p ∈ Cprev.carrier)
       (hpU : p ∈ U) :
       ∃ N ∈ 𝓝 p, IsOpen N ∧ p ∈ N ∧
         ∀ q, q ∈ N -> q ∈ U ->
           ∃ Cnext : BHW.BHWJostLocalScalarContinuationChart hd n τ U,
           ∃ P : Set (Fin n -> Fin (d + 1) -> ℂ),
             p ∈ P ∧ q ∈ Cnext.carrier ∧
             IsOpen P ∧ IsPreconnected P ∧ P.Nonempty ∧
             P ⊆ Cprev.carrier ∩ Cnext.carrier ∧
             Set.EqOn Cprev.branch Cnext.branch P

   structure BHW.BHWJostScalarTransitionData
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (Cleft Cright :
         BHW.BHWJostLocalScalarContinuationChart hd n τ U)
       (p q : Fin n -> Fin (d + 1) -> ℂ) where
     sourcePatch : Set (Fin n -> Fin (d + 1) -> ℂ)
     sourcePatch_open : IsOpen sourcePatch
     sourcePatch_preconnected : IsPreconnected sourcePatch
     sourcePatch_nonempty : sourcePatch.Nonempty
     source_mem : p ∈ sourcePatch
     target_mem : q ∈ Cright.carrier
     sourcePatch_sub :
       sourcePatch ⊆ Cleft.carrier ∩ Cright.carrier
     source_branch_agree :
       Set.EqOn Cleft.branch Cright.branch sourcePatch
     gramPatch : Set (Fin n -> Fin n -> ℂ)
     gramPatch_relOpen :
       IsRelOpenInSourceComplexGramVariety d n gramPatch
     gramPatch_preconnected : IsPreconnected gramPatch
     gramPatch_nonempty : gramPatch.Nonempty
     gramPatch_sub :
       gramPatch ⊆ Cleft.gramDomain ∩ Cright.gramDomain
     sourcePatch_gram_mem :
       ∀ y, y ∈ sourcePatch ->
         BHW.sourceMinkowskiGram d n y ∈ gramPatch
     gram_phi_agree :
       Set.EqOn Cleft.Phi Cright.Phi gramPatch

   structure BHW.BHWJostSourceNormalFormGeometryPatch
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (center : Fin n -> Fin (d + 1) -> ℂ) where
     carrier : Set (Fin n -> Fin (d + 1) -> ℂ)
     carrier_open : IsOpen carrier
     carrier_preconnected : IsPreconnected carrier
     center_mem : center ∈ carrier
     carrier_sub_U : carrier ⊆ U
     gramDomain : Set (Fin n -> Fin n -> ℂ)
     gram_relOpen :
       IsRelOpenInSourceComplexGramVariety d n gramDomain
     gram_preconnected : IsPreconnected gramDomain
     gram_sub_variety :
       gramDomain ⊆ sourceComplexGramVariety d n
     gram_mem :
       ∀ z, z ∈ carrier ->
         BHW.sourceMinkowskiGram d n z ∈ gramDomain

   theorem BHW.bhw_jost_sourceNormalFormGeometryPatch_at
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hU_open : IsOpen U)
       (hU_sub_ambient :
         U ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       {center : Fin n -> Fin (d + 1) -> ℂ}
       (hcenter : center ∈ U) :
       BHW.BHWJostSourceNormalFormGeometryPatch hd n τ U center

   theorem BHW.bhw_jost_uniformDescent_on_sourceNormalFormPatch
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       {center : Fin n -> Fin (d + 1) -> ℂ}
       (G : BHW.BHWJostSourceNormalFormGeometryPatch hd n τ U center)
       (Cprev : BHW.BHWJostLocalScalarContinuationChart hd n τ U)
       {p q : Fin n -> Fin (d + 1) -> ℂ}
       (hpG : p ∈ G.carrier)
       (hqG : q ∈ G.carrier)
       (hpC : p ∈ Cprev.carrier) :
       ∃ Cnext : BHW.BHWJostLocalScalarContinuationChart hd n τ U,
         BHW.BHWJostScalarTransitionData hd n τ U Cprev Cnext p q

   structure BHW.BHWJostBranchFreeTransferNeighborhood
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (center : Fin n -> Fin (d + 1) -> ℂ) where
     N : Set (Fin n -> Fin (d + 1) -> ℂ)
     N_mem_nhds : N ∈ 𝓝 center
     N_open : IsOpen N
     center_mem : center ∈ N
     transfer :
       ∀ p q, p ∈ N -> p ∈ U -> q ∈ N -> q ∈ U ->
       ∀ Cprev : BHW.BHWJostLocalScalarContinuationChart hd n τ U,
         p ∈ Cprev.carrier ->
           ∃ Cnext : BHW.BHWJostLocalScalarContinuationChart hd n τ U,
             BHW.BHWJostScalarTransitionData hd n τ U Cprev Cnext p q

   theorem BHW.bhw_jost_branchFreeTransferNeighborhood_at
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (hU_open : IsOpen U)
       (hU_sub_ambient :
         U ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       {p : Fin n -> Fin (d + 1) -> ℂ}
       (hpU : p ∈ U) :
       BHW.BHWJostBranchFreeTransferNeighborhood hd n τ U p

   structure BHW.UnitIntervalOrderedSubdivision
       {ι : Type} (c : ι -> Set unitInterval) where
     m : Nat
     t : Fin (m + 1) -> unitInterval
     t_zero : t 0 = 0
     t_last : t (Fin.last m) = 1
     t_mono : Monotone t
     interval_sub :
       ∀ j : Fin m, ∃ a : ι,
         Set.Icc (t (Fin.castSucc j)) (t j.succ) ⊆ c a

   theorem BHW.exists_unitInterval_orderedSubdivision_of_openCover
       {ι : Type} (c : ι -> Set unitInterval)
       (hc_open : ∀ a, IsOpen (c a))
       (hc_cover : Set.univ ⊆ ⋃ a, c a) :
       Nonempty (BHW.UnitIntervalOrderedSubdivision c)

   noncomputable def BHW.unitInterval_orderedSubdivision_of_openCover
       {ι : Type} (c : ι -> Set unitInterval)
       (hc_open : ∀ a, IsOpen (c a))
       (hc_cover : Set.univ ⊆ ⋃ a, c a) :
       BHW.UnitIntervalOrderedSubdivision c

   theorem BHW.exists_open_preconnected_neighborhood_subset
       {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
       {s : Set E} {p : E}
       (hs : IsOpen s) (hp : p ∈ s) :
       ∃ P : Set E,
         p ∈ P ∧ IsOpen P ∧ IsPreconnected P ∧
         P.Nonempty ∧ P ⊆ s

   theorem BHW.bhw_jost_continuationChain_of_compactPath
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hΩ0_sub_ambient :
         Ω0 ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (hU_sub_ambient :
         U ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p z : Fin n -> Fin (d + 1) -> ℂ}
       (hp0 : p ∈ Ω0 ∩ U)
       (γ : Path p z)
       (hγU : ∀ t, γ t ∈ U) :
       BHW.BHWSourcePatchContinuationChain hd n τ Ω0 U B0 p z
   ```

   The strict-route proof of
   `bhw_jost_initialOrientedContinuationChart_at` is the local
   Hall-Wightman/Jost descent theorem on the starting sector `Ω0`.  The
   near-identity proper-complex Lorentz theorem gives local constancy of `B0`
   along determinant-one complex Lorentz fibres.  The oriented normal-form
   source theorem then identifies those fibres, in max rank, with fibres of
   `sourceOrientedMinkowskiInvariant`; in lower rank it uses the documented
   Hall-Wightman singular contraction and continuity package.  Holomorphic
   descent gives a germ-holomorphic `Psi` on a preconnected oriented patch.
   Define `C.branch := Psi ∘ sourceOrientedMinkowskiInvariant`; then
   `branch_eq_orientedPullback` is definitional on the shrunk carrier,
   `branch_same_sourceOrientedInvariant` follows from the pullback formula,
   and `branch_complexLorentzInvariant` is
   `sourceOrientedMinkowskiInvariant_complexLorentzAction` followed by the
   pullback rewrite.  The returned source patch `P` is a preconnected
   shrink of `Ω0 ∩ C.carrier` around `p`, so `Set.EqOn C.branch B0 P`
   is the local descent normalization, not a global source-representative
   import.

   The strict-route one-step theorem propagates from an already constructed
   oriented chart by calling
   `bhw_jost_localOrientedDescent_from_chartBranch_star`.  That theorem
   produces an open star neighborhood `N ∈ 𝓝 p`, chosen before the endpoint
   `q` is fixed and small enough that the Hall-Wightman oriented
   source-normal-form chart at `p` and the chart at every `q ∈ N ∩ U` have a
   nonempty preconnected oriented overlap.  On that overlap the seed is not
   `B0`; it is exactly `Cprev.branch`.  Rewrite `Cprev.branch` as
   `Cprev.Psi ∘ sourceOrientedMinkowskiInvariant` by
   `Cprev.branch_eq_orientedPullback`; use
   `Cprev.branch_same_sourceOrientedInvariant` for representative
   independence; use `Cprev.branch_complexLorentzInvariant`, itself coming
   from `sourceOrientedMinkowskiInvariant_complexLorentzAction`, for the local
   proper-complex Lorentz constancy required by the Hall-Wightman descent; and
   apply the oriented regular/singular local continuation theorem to obtain
   `Cnext.Psi`.  The returned `BHWJostOrientedTransitionData` contains both
   the source overlap where the branches agree and the oriented overlap where
   `Cprev.Psi = Cnext.Psi`; these are the data consumed by the closed-loop
   monodromy theorem.

   In the conditional ordinary fork, the same proof reads with
   `sourceMinkowskiGram`, `Phi`, `branch_same_sourceGram`,
   `BHWJostScalarTransitionData`, and the full-component Hall-Wightman source
   input replacing the oriented names.  That fork is not the strict
   production route unless the full-component input is formally supplied.

   `BHW.bhw_jost_orientedSourceNormalFormGeometryPatch_at` is the
   branch-free geometry construction behind the strict compact-path cover.
   At `center ∈ U`, use `hU_open` to shrink inside `U` and
   `hU_sub_ambient` to invoke the local Hall-Wightman oriented
   source-normal-form theorem.  In max rank this is the
   `SourceOrientedMaxRankChartData` chart on a determinant-one full-frame
   patch; in lower rank it is the oriented rank-deficient Schur normal-form
   chart plus the normal-variety/removable-singularity packet already
   required for exceptional ranks.  The carrier is then shrunk by
   `BHW.exists_open_preconnected_neighborhood_subset`; `orientedDomain` is the
   corresponding relatively open preconnected patch in
   `sourceOrientedGramVariety`; `oriented_mem` records that every source point
   in the carrier is controlled by this one oriented invariant patch.

   `BHW.bhw_jost_uniformOrientedDescent_on_sourceNormalFormPatch` is where the
   scalar branch enters.  Given `p ∈ G.carrier`, `q ∈ G.carrier`, and an old
   oriented chart `Cprev` containing `p`, shrink an open preconnected
   `P ⊆ Cprev.carrier ∩ G.carrier` around `p`.  On the image of `P` under
   `sourceOrientedMinkowskiInvariant`, rewrite `Cprev.branch` as
   `Cprev.Psi ∘ sourceOrientedMinkowskiInvariant`;
   `Cprev.branch_same_sourceOrientedInvariant` makes this seed independent of
   source representatives and `Cprev.branch_complexLorentzInvariant` supplies
   the proper-complex Lorentz constancy needed by the local Hall-Wightman
   descent.  The oriented max-rank source chart, and in lower rank the
   oriented normal-variety Riemann extension theorem, continue that scalar
   germ to `G.orientedDomain`.  Define
   `Cnext.carrier := G.carrier`,
   `Cnext.orientedDomain := G.orientedDomain`, and
   `Cnext.branch := PsiNext ∘ sourceOrientedMinkowskiInvariant`; the `Cnext`
   fields are exactly `G.oriented_*`, `G.carrier_*`, the new
   `PsiNext_holo`, and
   `sourceOrientedMinkowskiInvariant_complexLorentzAction`.  The returned
   `BHWJostOrientedTransitionData` packages the source equality patch and the
   oriented patch where `Cprev.Psi = Cnext.Psi`.

   `BHW.bhw_jost_orientedBranchFreeTransferNeighborhood_at` is the
   non-circular cover theorem consumed by compact path subdivision.  For each
   `p ∈ U`, it chooses a geometry neighborhood `T.N ∈ 𝓝 p` before any
   continued branch is selected.  Its `transfer` field is uniform over the
   whole neighborhood: if `p' ∈ T.N ∩ U`, `q ∈ T.N ∩ U`, and an
   already-constructed oriented chart contains `p'`, then that chart can be
   continued to `q`, with an open preconnected overlap patch at `p'` on which
   the old and new branches agree.  The set `T.N` is determined by the
   Hall-Wightman oriented source-normal-form data and the ambient source-patch
   hull, not by the scalar branch; only the produced `Cnext.Psi` depends on
   `Cprev.branch`.  Its implementation is mechanical from the two lower
   surfaces above: take the geometry patch supplied by
   `bhw_jost_orientedSourceNormalFormGeometryPatch_at`, set `N := G.carrier`,
   and call the checked constructor
   `BHWJostOrientedBranchFreeTransferNeighborhood.ofSourceNormalFormPatch`;
   the constructor's `transfer` field is exactly
   `bhw_jost_uniformOrientedDescent_on_sourceNormalFormPatch G`.

   The conditional ordinary fork has the same branch-free topology transcript
   with `sourceMinkowskiGram`, `Phi`, `gramDomain`, and
   `BHWJostScalarTransitionData`; it remains downstream of the full-component
   Hall-Wightman source input.

   `BHW.exists_open_preconnected_neighborhood_subset` is the finite-dimensional
   topology shrinker used whenever the proof says "take a small connected
   patch."  From `hs : IsOpen s` and `hp : p ∈ s`, choose `ε > 0` with
   `Metric.ball p ε ⊆ s`; the ball is open and convex in the ambient real
   normed vector space, hence preconnected.  This supplies the preconnected
   local chart carriers, transition overlaps, common endpoint patch, and
   closing patch at `p0`.

   The compact-path theorem uses the pinned Mathlib topology API, not an
   informal finite-subdivision step.  The helper
   `BHW.exists_unitInterval_orderedSubdivision_of_openCover` is a thin
   `Nonempty` wrapper around
   `exists_monotone_Icc_subset_open_cover_unitInterval` from
   `Mathlib.Topology.UnitInterval`: it obtains
   `tN : Nat -> unitInterval`, `tN 0 = 0`, `Monotone tN`, an eventual index
   `m` with `∀ k ≥ m, tN k = 1`, and
   `∀ k, ∃ a, Set.Icc (tN k) (tN (k+1)) ⊆ c a`; then defines
   `t : Fin (m+1) -> unitInterval` by `t j := tN j.val`.  The endpoint proof
   is `hm m le_rfl`, monotonicity is inherited from `tN`, and
   `interval_sub j` is `hsub j.val`.  The data-valued selector
   `BHW.unitInterval_orderedSubdivision_of_openCover` is a
   `noncomputable def` by `Classical.choice`.  `Path.subpath` and `Path.concat` from
   `Mathlib.Topology.Subpath` provide the subpaths and their concatenation;
   the range inclusion for each subpath is
   `Path.range_subpath_of_le γ _ _ (S.t_mono (Fin.castSucc_le_succ j))`,
   followed by the stored `interval_sub j`.  The strict-route open cover used here
   is explicitly branch-free: for each `t : unitInterval`, apply
   `bhw_jost_orientedBranchFreeTransferNeighborhood_at` to `γ t`, and set
   `c t := γ ⁻¹' (T t).N`.  Continuity of `γ` and `(T t).N_open` give
   `IsOpen (c t)`, and `(T t).center_mem` gives the cover.  After
   subdivision, `interval_sub j`
   supplies an index `a` whose geometry neighborhood contains the whole
   subinterval.  Hence both
   `γ (S.t (Fin.castSucc j))` and `γ (S.t j.succ)` lie in `(T a).N`; applying
   `(T a).transfer` to the current chart at the left endpoint produces the
   next chart and a full `BHWJostOrientedTransitionData`.  Its source
   projection supplies the preconnected transition patch and
   `consecutive_agree`, while its oriented projection supplies the
   `Psi`-transition data for monodromy.
   This removes the circular cover "by the one-step neighborhoods of chains
   not yet constructed."  The chain producer then stores the resulting
   local oriented charts, branches, source transition patches, and oriented
   transitions in `BHWJostOrientedSourcePatchContinuationChain`.  The
   conditional ordinary fork is obtained by replacing the branch-free cover
   theorem and transition data with their plain-Gram names.

   Its own implementation split is:

   ```lean
   theorem BHW.bhw_local_complexLorentz_invariance_of_real_invariance
       [NeZero d] (hd : 2 <= d)
       (n : Nat)
       (Ω : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ_open : IsOpen Ω)
       (hB_holo : DifferentiableOn ℂ B Ω)
       (hB_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω ->
             B (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
       (z : Fin n -> Fin (d + 1) -> ℂ)
       (hz : z ∈ Ω) :
       ∃ C : Set (ComplexLorentzGroup d),
         IsOpen C ∧ (1 : ComplexLorentzGroup d) ∈ C ∧
         ∀ Λ, Λ ∈ C ->
           BHW.complexLorentzAction Λ z ∈ Ω ->
             B (BHW.complexLorentzAction Λ z) = B z

   theorem BHW.bhw_branch_constant_along_complexLorentz_path
       [NeZero d] (hd : 2 <= d)
       (n : Nat)
       (Ω : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ_open : IsOpen Ω)
       (hB_holo : DifferentiableOn ℂ B Ω)
       (hB_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω ->
             B (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
       {Λ0 Λ1 : ComplexLorentzGroup d}
       (γ : Path Λ0 Λ1)
       (z : Fin n -> Fin (d + 1) -> ℂ)
       (hγΩ : ∀ t, BHW.complexLorentzAction (γ t) z ∈ Ω) :
       B (BHW.complexLorentzAction Λ1 z) =
         B (BHW.complexLorentzAction Λ0 z)

   structure BHW.BHWSourcePatchContinuationChain
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (p0 z : Fin n -> Fin (d + 1) -> ℂ) where
     base_mem : p0 ∈ Ω0 ∩ U
     m : Nat
     node : Fin (m + 1) -> Fin n -> Fin (d + 1) -> ℂ
     node_zero : node 0 = p0
     node_last : node (Fin.last m) = z
     chart : Fin (m + 1) -> Set (Fin n -> Fin (d + 1) -> ℂ)
     node_mem : ∀ j, node j ∈ chart j
     localChart :
       Fin (m + 1) ->
         BHW.BHWJostLocalScalarContinuationChart hd n τ U
     branch : Fin (m + 1) ->
       (Fin n -> Fin (d + 1) -> ℂ) -> ℂ
     chart_open : ∀ j, IsOpen (chart j)
     chart_preconnected : ∀ j, IsPreconnected (chart j)
     chart_sub_U : ∀ j, chart j ⊆ U
     chart_eq_local : ∀ j, chart j = (localChart j).carrier
     branch_eq_local :
       ∀ j y, y ∈ chart j -> branch j y = (localChart j).branch y
     branch_holo : ∀ j, DifferentiableOn ℂ (branch j) (chart j)
     start_patch : Set (Fin n -> Fin (d + 1) -> ℂ)
     start_patch_open : IsOpen start_patch
     start_patch_preconnected : IsPreconnected start_patch
     start_patch_nonempty : start_patch.Nonempty
     start_mem : p0 ∈ start_patch
     start_patch_sub : start_patch ⊆ Ω0 ∩ chart 0
     start_agree :
       ∀ y, y ∈ start_patch -> branch 0 y = B0 y
     transition_patch :
       ∀ j : Fin m, Set (Fin n -> Fin (d + 1) -> ℂ)
     transition_patch_open : ∀ j, IsOpen (transition_patch j)
     transition_patch_nonempty : ∀ j, (transition_patch j).Nonempty
     transition_patch_preconnected : ∀ j, IsPreconnected (transition_patch j)
     transition_patch_sub_left :
       ∀ j, transition_patch j ⊆ chart (Fin.castSucc j)
     transition_patch_sub_right :
       ∀ j, transition_patch j ⊆ chart j.succ
     consecutive_agree :
       ∀ j : Fin m, ∀ y,
         y ∈ transition_patch j ->
           branch (Fin.castSucc j) y = branch j.succ y
     scalar_transition :
       ∀ j : Fin m,
         BHW.BHWJostScalarTransitionData hd n τ U
           (localChart (Fin.castSucc j)) (localChart j.succ)
           (node (Fin.castSucc j)) (node j.succ)
     final_mem : z ∈ chart (Fin.last m)
     chart_is_lorentz_step :
       ∀ j, ∃ Ωbase : Set (Fin n -> Fin (d + 1) -> ℂ),
         IsOpen Ωbase ∧
         Ωbase ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ ∧
         ∃ Λ : ComplexLorentzGroup d,
           chart j =
             (fun u => BHW.complexLorentzAction Λ u) '' Ωbase

   theorem BHW.bhw_sourcePatchHull_has_continuationChain
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hΩ0_sub_ambient :
         Ω0 ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hU_hull :
         ∃ z0, U = BHW.os45SourcePatchBHWJostHull d n τ z0)
       (hΩ0_meets_U : (Ω0 ∩ U).Nonempty)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z) :
       ∃ p0, p0 ∈ Ω0 ∩ U ∧
         ∀ z, z ∈ U ->
           BHW.BHWSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z

   noncomputable def BHW.bhw_continuedValueAlongChain
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       {p0 z : Fin n -> Fin (d + 1) -> ℂ}
       (C : BHW.BHWSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z) : ℂ :=
     C.branch (Fin.last C.m) z

   structure BHW.BHWJostClosedContinuationLoop
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (p0 : Fin n -> Fin (d + 1) -> ℂ) where
     chain :
       BHW.BHWSourcePatchContinuationChain hd n τ Ω0 U B0 p0 p0
     final_base_mem : p0 ∈ chain.chart (Fin.last chain.m)
     closing_patch : Set (Fin n -> Fin (d + 1) -> ℂ)
     closing_patch_open : IsOpen closing_patch
     closing_patch_preconnected : IsPreconnected closing_patch
     closing_patch_nonempty : closing_patch.Nonempty
     closing_patch_mem : p0 ∈ closing_patch
     closing_patch_sub_start :
       closing_patch ⊆ chain.start_patch
     closing_patch_sub_final :
       closing_patch ⊆ chain.chart (Fin.last chain.m)
     closing_gramPatch : Set (Fin n -> Fin n -> ℂ)
     closing_gramPatch_relOpen :
       IsRelOpenInSourceComplexGramVariety d n closing_gramPatch
     closing_gramPatch_preconnected : IsPreconnected closing_gramPatch
     closing_gramPatch_nonempty : closing_gramPatch.Nonempty
     closing_gramPatch_sub_start :
       closing_gramPatch ⊆ (chain.localChart 0).gramDomain
     closing_gramPatch_sub_final :
       closing_gramPatch ⊆
         (chain.localChart (Fin.last chain.m)).gramDomain
     closing_patch_gram_mem :
       ∀ y, y ∈ closing_patch ->
         BHW.sourceMinkowskiGram d n y ∈ closing_gramPatch

   theorem BHW.bhw_jost_closedChain_gramMonodromy_trivial
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L : BHW.BHWJostClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Phi
         (L.chain.localChart 0).Phi
         L.closing_gramPatch

   theorem BHW.bhw_jost_closedChain_regularGramMonodromy_trivial
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hD : d + 1 < n)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L : BHW.BHWJostClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Phi
         (L.chain.localChart 0).Phi
         (L.closing_gramPatch ∩
           BHW.sourceSymmetricRankExactStratum n (d + 1))

   theorem BHW.bhw_jost_closedChain_gramMonodromy_extend_from_regular
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hD : d + 1 < n)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L : BHW.BHWJostClosedContinuationLoop hd n τ Ω0 U B0 p0)
       (hreg :
         Set.EqOn
           (L.chain.localChart (Fin.last L.chain.m)).Phi
           (L.chain.localChart 0).Phi
           (L.closing_gramPatch ∩
             BHW.sourceSymmetricRankExactStratum n (d + 1))) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Phi
         (L.chain.localChart 0).Phi
         L.closing_gramPatch

   theorem BHW.bhw_jost_closedChain_gramMonodromy_easy
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hn : n <= d + 1)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L : BHW.BHWJostClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Phi
         (L.chain.localChart 0).Phi
         L.closing_gramPatch

   theorem BHW.bhw_jost_closedChain_monodromy_trivial
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L : BHW.BHWJostClosedContinuationLoop hd n τ Ω0 U B0 p0) :
       Set.EqOn (L.chain.branch (Fin.last L.chain.m)) B0 L.closing_patch

   theorem BHW.bhw_jost_terminalBranches_eq_of_closed_monodromy
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p0 z : Fin n -> Fin (d + 1) -> ℂ}
       (C₁ C₂ : BHW.BHWSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z) :
       ∃ P : Set (Fin n -> Fin (d + 1) -> ℂ),
         z ∈ P ∧ IsOpen P ∧ IsPreconnected P ∧
         P ⊆ C₁.chart (Fin.last C₁.m) ∩ C₂.chart (Fin.last C₂.m) ∧
         Set.EqOn
           (C₁.branch (Fin.last C₁.m))
           (C₂.branch (Fin.last C₂.m)) P

   theorem BHW.bhw_branch_chain_singleValued_on_sourcePatchHull
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hU_hull :
         ∃ z0, U = BHW.os45SourcePatchBHWJostHull d n τ z0)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z)
       {p0 z : Fin n -> Fin (d + 1) -> ℂ}
       (C₁ C₂ : BHW.BHWSourcePatchContinuationChain hd n τ Ω0 U B0 p0 z) :
       BHW.bhw_continuedValueAlongChain hd n τ Ω0 U B0 C₁ =
         BHW.bhw_continuedValueAlongChain hd n τ Ω0 U B0 C₂

   theorem BHW.bhw_continuationAtlas_from_chains
       [NeZero d] (hd : 2 <= d)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ0_open : IsOpen Ω0)
       (hU_open : IsOpen U)
       (hU_connected : IsConnected U)
       (hΩ0_sub_ambient :
         Ω0 ⊆ BHW.os45SourcePatchBHWJostAmbient d n τ)
       (hU_hull :
         ∃ z0, U = BHW.os45SourcePatchBHWJostHull d n τ z0)
       (hΩ0_meets_U : (Ω0 ∩ U).Nonempty)
       (hB0_holo : DifferentiableOn ℂ B0 Ω0)
       (hB0_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω0 ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω0 ->
             B0 (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B0 z) :
       BHW.BHWSourcePatchContinuationAtlas hd n τ Ω0 U B0
   ```

   The first theorem is the near-identity identity theorem in the
   proper-complex Lorentz group.  The second theorem covers the compact
   interval of a group `Path` by finitely many translated near-identity
   neighborhoods and composes the local constancy equalities.  The
   chain-carrier theorem is the only place where the definition of the
   source-patch hull is used.  It first chooses one fixed base point
   `p0 ∈ Ω0 ∩ U` from `hΩ0_meets_U`.  Since `U` is the path component of the
   open ambient, `pathComponentIn_subset` gives
   `hU_sub_ambient : U ⊆ os45SourcePatchBHWJostAmbient d n τ`, and every
   `z ∈ U` is joined to this same `p0` by a path in `U`.  The compact-path
   theorem is then called with `hΩ0_sub_ambient` and this derived
   `hU_sub_ambient`; compactness of the path gives a finite cover by BHW/Jost
   continuation charts with explicit open preconnected transition patches
   between consecutive charts.  The chain stores
   `start_mem : p0 ∈ start_patch` and `start_patch_preconnected`, so the
   initial normalization is a fixed base patch, not an anonymous nonempty
   overlap somewhere in `Ω0`.

   The single-valuedness theorem is no longer a slogan about closed chains.
   The chain now stores enough scalar data to state the real obstruction.  Each
   entry `C.scalar_transition j` contains both the source overlap used for
   `consecutive_agree` and the relatively open preconnected Gram overlap on
   which the scalar representatives
   `(C.localChart (Fin.castSucc j)).Phi` and
   `(C.localChart j.succ).Phi` agree.  A closed loop also stores
   `closing_gramPatch`, a relatively open preconnected patch in the
   intersection of the initial and final Gram domains, and a map from the
   source closing patch into it.

   In the conditional ordinary fork, the separate theorem
   `bhw_jost_closedChain_gramMonodromy_trivial` is the Hall-Wightman/Jost
   monodromy theorem after the full-component scalar-product input has been
   supplied.  Its proof is split by arity.
   In the easy case `n <= d + 1`, the source complex Gram variety is the full
   symmetric coordinate space; `bhw_jost_closedChain_gramMonodromy_easy`
   proves trivial monodromy by ordinary SCV analytic continuation on the
   preconnected coordinate patches carried by the scalar transitions.  In the
   hard case `d + 1 < n`,
   `bhw_jost_closedChain_regularGramMonodromy_trivial` first proves equality
   on
   `closing_gramPatch ∩ sourceSymmetricRankExactStratum n (d + 1)`.  This is
   the ordinary-fork Hall-Wightman regular-stratum monodromy input: the finite
   scalar-transition chain is refined inside the smooth rank-exact source-Gram
   stratum, where the source-normal-form charts are biholomorphic and the
   transition equalities are equalities of ordinary holomorphic functions on
   nonempty connected overlaps.  The loop is the one obtained from proper
   complex Lorentz/Jost source-normal-form continuation inside the selected
   source-patch hull; no PET, `fullExtendF`, common-boundary envelope, or final
   locality may enter here.  Finally
   `bhw_jost_closedChain_gramMonodromy_extend_from_regular` extends equality
   from the dense rank-exact part to all of `closing_gramPatch` by applying
   `SourceVarietyGermHolomorphicOn.sub`,
   `SourceVarietyGermHolomorphicOn.continuousOn`, and the already pinned
   normal-variety/removable-singularity density theorem
   `sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact` on the
   relatively open patch `closing_gramPatch`.

   The source-level theorem `bhw_jost_closedChain_monodromy_trivial` is then
   mechanical inside that ordinary fork.  On the strict proper-complex route,
   the identical proof script uses `closing_orientedPatch`,
   `branch_eq_orientedPullback`, and
   `bhw_jost_closedChain_orientedMonodromy_trivial` instead of the three
   plain-Gram fields.  For `y ∈ L.closing_patch`, use
   `L.closing_patch_gram_mem` to put `G := sourceMinkowskiGram d n y` in
   `L.closing_gramPatch`.  The Gram monodromy theorem gives equality of the
   final and initial `Phi` values at `G`.  The fields
   `branch_eq_local` and each local chart's `branch_eq_pullback` rewrite the
   final and initial source branches to those two `Phi` values.  Since
   `L.closing_patch_sub_start hy` puts `y` in `chain.start_patch`,
   `chain.start_agree y` rewrites the initial source branch to `B0 y`.
   Thus
   `L.chain.branch (Fin.last L.chain.m) y = B0 y`.

   The comparison theorem must be read with the same provenance warning as
   the oriented route.  A bare scalar chain is not enough to concatenate
   `C₁` with a stored reverse of `C₂` unless the transition data are
   symmetric and the terminal bridge is produced as an output rather than used
   as an input.  The active strict route therefore uses transfer traces and
   one-step uniqueness: closed-chain monodromy gives equality on a base
   closing patch for a source-backed return trace, and finite uniqueness
   transports that equality forward to the endpoint patch.  The public
   `bhw_branch_chain_singleValued_on_sourcePatchHull` is just evaluation of
   this produced endpoint-overlap equality at `z`.

   The atlas theorem chooses the fixed `p0` once, includes the restricted
   starting chart `Ω0 ∩ U` with the branch `B0` restricted to that open subset
   of `U`, and then indexes the terminal charts of all finite chains from that
   `p0`.  It uses each chain's terminal `branch (Fin.last C.m)` as the local
   branch, uses
   `bhw_continuedValueAlongChain` only as the point-value projection of that
   branch, uses single-valuedness for overlap compatibility, and proves
   `base_agree` by comparing any terminal chain chart meeting `Ω0 ∩ U` with
   the explicit restricted starting chart.  The public
   `bargmannHallWightman_continue_branch_on_sourcePatchHull` is
   `bhw_continuationAtlas_from_chains` followed by
   `bhw_glue_sourcePatchContinuationAtlas`.

   The first local theorem is not implemented through an abstract
   `LocalHomeomorph` placeholder.  It is now checked in
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceOrientedBHWInvariance.lean`,
   by exposing the existing exponential-neighborhood machinery in
   `ComplexLieGroups/Connectedness/ComplexInvariance/Core.lean` at the
   BHW-Jost boundary.  The checked public support surfaces are:

   ```lean
   theorem BHW.complexLorentz_exp_nhd_of_one
       (ε : ℝ) (hε : 0 < ε) :
       ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
         ∃ X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ,
           ComplexLorentzGroup.IsInLieAlgebra X ∧
           Λ.val = NormedSpace.exp X ∧
           ‖X‖ < ε

   def BHW.reMatrixCLie
       (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
       Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i j => (X i j).re

   def BHW.imMatrixCLie
       (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
       Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i j => (X i j).im

   theorem BHW.reMatrixCLie_isInLorentzAlgebra
       {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
       (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
       IsInLorentzAlgebra d (BHW.reMatrixCLie X)

   theorem BHW.imMatrixCLie_isInLorentzAlgebra
       {X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
       (hX : ComplexLorentzGroup.IsInLieAlgebra X) :
       IsInLorentzAlgebra d (BHW.imMatrixCLie X)

   theorem BHW.matrix_re_im_decomp_CLie
       (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
       X =
         (BHW.reMatrixCLie X).map Complex.ofReal +
           Complex.I • (BHW.imMatrixCLie X).map Complex.ofReal

   theorem BHW.exp_map_ofReal_bridge
       (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (s : ℝ) :
       (NormedSpace.exp (s • Y) :
           Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).map Complex.ofReal =
         (NormedSpace.exp ((s : ℂ) • Y.map Complex.ofReal) :
           Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)

   theorem BHW.bhw_near_identity_invariance_on_open
       (n : Nat)
       (Ω : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ_open : IsOpen Ω)
       (hB_holo : DifferentiableOn ℂ B Ω)
       (hB_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω ->
             B (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
       (z : Fin n -> Fin (d + 1) -> ℂ)
       (hz : z ∈ Ω) :
       ∀ᶠ Λ in 𝓝 (1 : ComplexLorentzGroup d),
         BHW.complexLorentzAction Λ z ∈ Ω ->
           B (BHW.complexLorentzAction Λ z) = B z

   theorem BHW.bhw_local_complexLorentz_invariance_of_real_invariance
       (n : Nat)
       (Ω : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ_open : IsOpen Ω)
       (hB_holo : DifferentiableOn ℂ B Ω)
       (hB_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω ->
             B (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
       (z : Fin n -> Fin (d + 1) -> ℂ)
       (hz : z ∈ Ω) :
       ∃ C : Set (ComplexLorentzGroup d),
         IsOpen C ∧ (1 : ComplexLorentzGroup d) ∈ C ∧
           ∀ Λ, Λ ∈ C ->
             BHW.complexLorentzAction Λ z ∈ Ω ->
               B (BHW.complexLorentzAction Λ z) = B z

   theorem BHW.bhw_branch_constant_along_complexLorentz_path
       (n : Nat)
       (Ω : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hΩ_open : IsOpen Ω)
       (hB_holo : DifferentiableOn ℂ B Ω)
       (hB_realLorentz :
         ∀ R : RestrictedLorentzGroup d, ∀ z, z ∈ Ω ->
           BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ Ω ->
             B (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal R) z) = B z)
       {Λ0 Λ1 : ComplexLorentzGroup d}
       (γ : Path Λ0 Λ1)
       (z : Fin n -> Fin (d + 1) -> ℂ)
       (hγΩ : ∀ t : unitInterval,
         BHW.complexLorentzAction (γ t) z ∈ Ω) :
       B (BHW.complexLorentzAction Λ1 z) =
         B (BHW.complexLorentzAction Λ0 z)

   theorem BHW.BHWJostLocalOrientedContinuationChart.branch_constant_along_complexLorentz_path
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       (C : BHW.BHWJostLocalOrientedContinuationChart hd n τ U)
       {Λ0 Λ1 : ComplexLorentzGroup d}
       (γ : Path Λ0 Λ1)
       (z : Fin n -> Fin (d + 1) -> ℂ)
       (hγC : ∀ t : unitInterval,
         BHW.complexLorentzAction (γ t) z ∈ C.carrier) :
       C.branch (BHW.complexLorentzAction Λ1 z) =
         C.branch (BHW.complexLorentzAction Λ0 z)

   theorem BHW.BHWJostOrientedSourcePatchContinuationChain
       .terminal_Psi_eq_initial_Psi_of_mem_all_orientedTransitions
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       {B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
       {p0 z : Fin n -> Fin (d + 1) -> ℂ}
       (C :
         BHW.BHWJostOrientedSourcePatchContinuationChain
           hd n τ Ω0 U B0 p0 z)
       {G : BHW.SourceOrientedGramData d n}
       (hGtrans :
         ∀ j : Fin C.m, G ∈ (C.oriented_transition j).orientedPatch) :
       (C.localChart (Fin.last C.m)).Psi G = (C.localChart 0).Psi G

   theorem BHW.BHWJostOrientedTransitionData.propagate_eqOn_to_right_maxRank
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       {Cleft Cright : BHW.BHWJostLocalOrientedContinuationChart hd n τ U}
       {p q : Fin n -> Fin (d + 1) -> ℂ}
       (hn : d + 1 <= n)
       (T :
         BHW.BHWJostOrientedTransitionData hd n τ U Cleft Cright p q)
       {Φ : BHW.SourceOrientedGramData d n -> ℂ}
       {D seed : Set (BHW.SourceOrientedGramData d n)}
       (hD_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n D)
       (hDmax_conn :
         IsConnected (D ∩ {G | BHW.SourceOrientedMaxRankAt d n G}))
       (hD_sub_left : D ⊆ Cleft.orientedDomain)
       (hΦ : BHW.SourceOrientedVarietyGermHolomorphicOn d n Φ D)
       (hseed_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n seed)
       (hseed_nonempty : seed.Nonempty)
       (hseed_sub_D : seed ⊆ D)
       (hseed_sub_max : seed ⊆ {G | BHW.SourceOrientedMaxRankAt d n G})
       (hseed_eq : Set.EqOn Φ Cleft.Psi seed)
       (hT_sub_D : T.orientedPatch ⊆ D) :
       Set.EqOn Φ Cright.Psi
         (T.orientedPatch ∩ {G | BHW.SourceOrientedMaxRankAt d n G})

   theorem BHW.exists_maxRankSeed_eqOn_of_connected_domain
       (hn : d + 1 <= n)
       {Φ Ψ : BHW.SourceOrientedGramData d n -> ℂ}
       {D seed W : Set (BHW.SourceOrientedGramData d n)}
       (hD_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n D)
       (hDmax_conn :
         IsConnected (D ∩ {G | BHW.SourceOrientedMaxRankAt d n G}))
       (hΦ : BHW.SourceOrientedVarietyGermHolomorphicOn d n Φ D)
       (hΨ : BHW.SourceOrientedVarietyGermHolomorphicOn d n Ψ D)
       (hseed_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n seed)
       (hseed_nonempty : seed.Nonempty)
       (hseed_sub_D : seed ⊆ D)
       (hseed_sub_max : seed ⊆ {G | BHW.SourceOrientedMaxRankAt d n G})
       (hseed_eq : Set.EqOn Φ Ψ seed)
       (hW_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n W)
       (hW_nonempty : W.Nonempty)
       (hW_sub_D : W ⊆ D) :
       ∃ seedNext : Set (BHW.SourceOrientedGramData d n),
         BHW.IsRelOpenInSourceOrientedGramVariety d n seedNext ∧
         IsPreconnected seedNext ∧
         seedNext.Nonempty ∧
         seedNext ⊆ W ∩ {G | BHW.SourceOrientedMaxRankAt d n G} ∧
         Set.EqOn Φ Ψ seedNext

   theorem BHW.BHWJostOrientedTransitionData.exists_propagatedSeed_to_right
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       {Cleft Cright : BHW.BHWJostLocalOrientedContinuationChart hd n τ U}
       {p q : Fin n -> Fin (d + 1) -> ℂ}
       (hn : d + 1 <= n)
       (T :
         BHW.BHWJostOrientedTransitionData hd n τ U Cleft Cright p q)
       {Φ : BHW.SourceOrientedGramData d n -> ℂ}
       {D seed : Set (BHW.SourceOrientedGramData d n)}
       (hD_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n D)
       (hDmax_conn :
         IsConnected (D ∩ {G | BHW.SourceOrientedMaxRankAt d n G}))
       (hD_sub_left : D ⊆ Cleft.orientedDomain)
       (hΦ : BHW.SourceOrientedVarietyGermHolomorphicOn d n Φ D)
       (hseed_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n seed)
       (hseed_nonempty : seed.Nonempty)
       (hseed_sub_D : seed ⊆ D)
       (hseed_sub_max : seed ⊆ {G | BHW.SourceOrientedMaxRankAt d n G})
       (hseed_eq : Set.EqOn Φ Cleft.Psi seed)
       (hT_sub_D : T.orientedPatch ⊆ D) :
       ∃ seedNext : Set (BHW.SourceOrientedGramData d n),
         BHW.IsRelOpenInSourceOrientedGramVariety d n seedNext ∧
         IsPreconnected seedNext ∧
         seedNext.Nonempty ∧
         seedNext ⊆
           T.orientedPatch ∩ {G | BHW.SourceOrientedMaxRankAt d n G} ∧
         Set.EqOn Φ Cright.Psi seedNext

   def BHW.BHWJostOrientedMaxRankClosedLoopSeed.of_sourceRealized_branch_eq
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       {B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       {L : BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}
       {seed : Set (BHW.SourceOrientedGramData d n)}
       (hseed_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n seed)
       (hseed_pre : IsPreconnected seed)
       (hseed_nonempty : seed.Nonempty)
       (hseed_sub :
         seed ⊆ L.closing_orientedPatch ∩
           {G | BHW.SourceOrientedMaxRankAt d n G})
       (hsource_eq :
         ∀ G, G ∈ seed ->
           ∃ y0 yF,
             y0 ∈ (L.chain.localChart 0).carrier ∧
             yF ∈ (L.chain.localChart (Fin.last L.chain.m)).carrier ∧
             BHW.sourceOrientedMinkowskiInvariant d n y0 = G ∧
             BHW.sourceOrientedMinkowskiInvariant d n yF = G ∧
             (L.chain.localChart (Fin.last L.chain.m)).branch yF =
               (L.chain.localChart 0).branch y0) :
       BHW.BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L

   def BHW.BHWJostOrientedMaxRankClosedLoopSeed.of_commonTransitionSeed
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       {B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       {L : BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}
       {seed : Set (BHW.SourceOrientedGramData d n)}
       (hseed_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n seed)
       (hseed_pre : IsPreconnected seed)
       (hseed_nonempty : seed.Nonempty)
       (hseed_closing : seed ⊆ L.closing_orientedPatch)
       (hseed_max : seed ⊆ {G | BHW.SourceOrientedMaxRankAt d n G})
       (hseed_trans :
         ∀ j : Fin L.chain.m,
           seed ⊆ (L.chain.oriented_transition j).orientedPatch) :
       BHW.BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L

   theorem BHW.BHWJostOrientedMaxRankClosedLoopSeed
       .exists_of_connectedDomainPropagation
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       {B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       {L : BHW.BHWJostOrientedClosedContinuationLoop hd n τ Ω0 U B0 p0}
       (hn : d + 1 <= n)
       {D seed : Set (BHW.SourceOrientedGramData d n)}
       (hD_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n D)
       (hDmax_conn :
         IsConnected (D ∩ {G | BHW.SourceOrientedMaxRankAt d n G}))
       (hD_sub_final :
         D ⊆ (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
       (hD_sub_start : D ⊆ (L.chain.localChart 0).orientedDomain)
       (hseed_rel : BHW.IsRelOpenInSourceOrientedGramVariety d n seed)
       (hseed_nonempty : seed.Nonempty)
       (hseed_sub_D : seed ⊆ D)
       (hseed_sub_max : seed ⊆ {G | BHW.SourceOrientedMaxRankAt d n G})
       (hseed_eq :
         Set.EqOn
           (L.chain.localChart (Fin.last L.chain.m)).Psi
           (L.chain.localChart 0).Psi
           seed)
       (hclosing_sub_D : L.closing_orientedPatch ⊆ D) :
       Nonempty (BHW.BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L)
   ```

   `BHW.complexLorentz_exp_nhd_of_one` is the public form of the existing
   private `exp_nhd_of_one`: the matrix exponential maps a sufficiently small
   neighborhood of `0` in the complex Lorentz Lie algebra onto a neighborhood
   of `1` in `ComplexLorentzGroup d`, with a norm-controlled logarithm.  The
   real/imaginary support lemmas are the current private `reMatrix`,
   `imMatrix`, `matrix_re_im_decomp`, `reMatrix_isInLorentzAlgebra`,
   `imMatrix_isInLorentzAlgebra`, and `exp_map_ofReal_bridge` made available
   at the BHW-Jost boundary.

   The proof of `bhw_near_identity_invariance_on_open` is an implementation
   copy of the already checked `near_identity_core`, with `ForwardTube d n`
   replaced by the arbitrary open set `Ω` and the real-invariance hypothesis
   made conditional on both real-orbit points lying in `Ω`; the norm estimates
   are checked as private helpers in the same file:

   1. Continuity of
      `A ↦ fun k μ => ∑ ν, (NormedSpace.exp A) μ ν * z k ν`, plus
      `hΩ_open` and `hz`, gives `δ > 0` such that `‖A‖ < δ` implies
      `exp(A) · z ∈ Ω`.
   2. Apply `BHW.complexLorentz_exp_nhd_of_one (δ / 7)` and write every
      nearby `Λ` as `Λ.val = exp X` with `X ∈ so(1,d;ℂ)` and `‖X‖ < δ/7`.
   3. Decompose
      `X = X₁ + I • X₂` with
      `X₁ = (reMatrixCLie X).map Complex.ofReal` and
      `X₂ = (imMatrixCLie X).map Complex.ofReal`; both real parts lie in
      `so(1,d;ℝ)`.
   4. For real `s` with `‖(s : ℂ)‖ < 2`, the bridge lemma identifies
      `exp(X₁ + (s : ℂ) • X₂)` with
      `ComplexLorentzGroup.ofReal (expLorentz d (Y₁ + s • Y₂) ...)`.
      The norm bound keeps the orbit in `Ω`, so `hB_realLorentz` gives
      `B(exp(X₁ + (s : ℂ) • X₂) · z) = B z`.
   5. The one-variable function
      `g s = B(exp(X₁ + s • X₂) · z) - B z` is holomorphic on
      `Metric.ball 0 2`; it vanishes on a punctured real set accumulating at
      `0`; `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`
      on the convex ball gives `g = 0` there.  Evaluating at `s = I` and using
      the decomposition of `X` proves the desired equality.

   `bhw_local_complexLorentz_invariance_of_real_invariance` then converts the
   filter statement into an open set `C` by
   `Filter.Eventually.exists_mem` and `mem_nhds_iff`.  This is a
   determinant-one/proper-complex `SO(1,d;ℂ)` argument throughout; no
   `O(1,d;ℂ)` or improper component is introduced.

   `bhw_branch_constant_along_complexLorentz_path` is checked from the local
   theorem by local constancy on `unitInterval`.  For
   `γ : Path Λ0 Λ1`, define
   `f t := B (complexLorentzAction (γ t) z)`.  At `t0`, apply the local
   theorem to `z0 := complexLorentzAction (γ t0) z`; continuity of
   `t ↦ γ t * (γ t0)⁻¹` and openness of the returned neighborhood `C` give
   `f t = f t0` eventually near `t0`, using
   `complexLorentzAction_mul` to rewrite
   `(γ t * (γ t0)⁻¹) · ((γ t0) · z)` as `(γ t) · z`.  Hence `f` is locally
   constant, and `unitInterval` is preconnected, so
   `IsLocallyConstant.apply_eq_of_isPreconnected` gives `f 1 = f 0`.  The
   chart-specialized theorem is this path theorem with
   `Ω := C.carrier`, `B := C.branch`, `hΩ_open := C.carrier_open`,
   `hB_holo := C.branch_holo`, and the real-Lorentz hypothesis supplied by
   `C.branch_complexLorentzInvariant (ComplexLorentzGroup.ofReal R)`.

   `BHWJostOrientedMaxRankClosedLoopSeed.of_sourceRealized_branch_eq` is the
   checked seed-constructor bridge used immediately after the genuine
   finite-overlap BHW/Jost argument has produced equality of the terminal and
   initial chart branches on source representatives of a nonempty relatively
   open max-rank seed.  The implementation fills the structure fields
   directly from `hseed_rel`, `hseed_pre`, `hseed_nonempty`, and `hseed_sub`.
   For the `seed_eq` field, it takes `G ∈ seed`, extracts source
   representatives `y0`, `yF` from `hsource_eq`, rewrites both branch values
   through the already stored `branch_eq_orientedPullback` fields of the
   initial and final charts, and composes those rewrites with the supplied
   source-level branch equality.  Thus the next remaining theorem must produce
   `hsource_eq`; no further Lean-level packaging is hidden there.

   The checked finite-chain telescope is the other mechanical exit.  For a
   fixed oriented invariant `G`, define
   `f j := (C.localChart j).Psi G`.  Each stored oriented transition gives
   `f j.castSucc = f j.succ` whenever `G` lies in that transition's
   `orientedPatch`.  A private finite `Fin` lemma upgrades adjacent equality
   along `Fin (m + 1)` to `f (Fin.last m) = f 0`.  Therefore a seed contained
   in every transition oriented patch gives terminal/initial `Psi` equality
   pointwise, and `of_commonTransitionSeed` packages it with the supplied
   relative-openness, preconnectedness, nonemptiness, closing-patch
   containment, and max-rank containment.  This is only a sufficient telescope
   case: for a moving continuation chain the intersection of all transition
   patches need not be nonempty.  The faithful next theorem is therefore a
   propagated-seed step: carry a nonempty relatively open max-rank equality
   seed across one transition by an identity-principle argument on a connected
   intermediate oriented domain, producing a new seed for the next transition.
   Iterating that propagated-seed step is the Lean-ready form of the
   Hall-Wightman/Jost finite-overlap argument; its output feeds the more
   general source-realized equality constructor above.

   The next theorem surface should make the finite-overlap data explicit
   before trying to prove that data exists.  A faithful Lean shape is:

   ```lean
   structure BHW.BHWJostOrientedFiniteOverlapPropagationData
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       {B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L : BHW.BHWJostOrientedClosedContinuationLoop
         hd n τ Ω0 U B0 p0) where
     hn : d + 1 <= n
     terminalDomain : Set (BHW.SourceOrientedGramData d n)
     terminalDomain_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n terminalDomain
     terminalDomain_maxRank_connected :
       IsConnected
         (terminalDomain ∩ {G | BHW.SourceOrientedMaxRankAt d n G})
     terminalDomain_sub_final :
       terminalDomain ⊆
         (L.chain.localChart (Fin.last L.chain.m)).orientedDomain
     terminalDomain_sub_start :
       terminalDomain ⊆ (L.chain.localChart 0).orientedDomain
     terminalSeed : Set (BHW.SourceOrientedGramData d n)
     terminalSeed_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n terminalSeed
     terminalSeed_nonempty : terminalSeed.Nonempty
     terminalSeed_sub_domain : terminalSeed ⊆ terminalDomain
     terminalSeed_sub_max :
       terminalSeed ⊆ {G | BHW.SourceOrientedMaxRankAt d n G}
     terminalSeed_eq :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         terminalSeed
     closingPatch_sub_terminalDomain :
       L.closing_orientedPatch ⊆ terminalDomain
   ```

   Its consumer is completely mechanical:

   ```lean
   theorem BHW.BHWJostOrientedFiniteOverlapPropagationData
       .to_closedLoopSeed
       (P : BHW.BHWJostOrientedFiniteOverlapPropagationData L) :
       Nonempty
         (BHW.BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L)
   ```

   The proof is exactly
   `BHWJostOrientedMaxRankClosedLoopSeed.exists_of_connectedDomainPropagation`
   applied to the fields of `P`.  This structure is not the hard theorem; it
   is the honest terminal interface for the hard theorem.

   The terminal monodromy consumers are also checked directly:

   ```lean
   theorem BHW.BHWJostOrientedFiniteOverlapPropagationData
       .to_orientedMonodromy
       (P : BHW.BHWJostOrientedFiniteOverlapPropagationData L)
       (hclosing_max_conn :
         IsConnected
           (L.closing_orientedPatch ∩
             {G | BHW.SourceOrientedMaxRankAt d n G})) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         L.closing_orientedPatch

   theorem BHW.BHWJostOrientedFiniteOverlapPropagationData
       .to_sourceMonodromy_headSliceIFT
       (P : BHW.BHWJostOrientedFiniteOverlapPropagationData L) :
       Set.EqOn
         (L.chain.branch (Fin.last L.chain.m))
         B0
         L.closing_patch
   ```

   Thus an accumulated-germ finite-overlap proof may target
   `BHWJostOrientedFiniteOverlapPropagationData L` directly and close the
   source monodromy goal with `P.to_sourceMonodromy_headSliceIFT`, without
   proving that every intermediate step domain lies in the original chart-0
   domain.

   The smaller terminal-seed boundary is checked too.  If the accumulated-germ
   proof has already reached a nonempty relatively open max-rank seed
   `terminalSeed ⊆ L.closing_orientedPatch` on which the terminal and initial
   oriented germs agree, then
   `BHWJostOrientedFiniteOverlapPropagationData.of_terminalSeedOnClosingPatch_headSliceIFT`
   chooses `L.closing_orientedPatch` as the terminal domain, derives its
   max-rank connectedness by the head-slice IFT theorem, and packages the data.
   The one-line source-monodromy endpoint is
   `BHWJostOrientedFiniteOverlapPropagationData.sourceMonodromy_of_terminalSeedOnClosingPatch_headSliceIFT`.
   Therefore the accumulated-germ positive-length proof does not have to
   manufacture a separate terminal domain if its final equality seed already
   lies inside the closing oriented patch.

   The producer-facing package for that smaller route is also checked:
   `BHWJostOrientedClosingPatchTerminalSeedData L` stores `hn`, a terminal
   seed, relative openness, nonemptiness, max-rank containment, containment in
   `L.closing_orientedPatch`, and terminal/initial oriented-germ equality on
   that seed.  Its constructor
   `of_sourceRealized_branch_eq` consumes the more natural Hall-Wightman/Jost
   output: for each `G` in the terminal seed, source representatives `y0` and
   `yF` in the initial and terminal carriers with oriented invariant `G`, plus
   equality of the corresponding source branches.  The constructor rewrites
   both sides through `branch_eq_orientedPullback`, so the hard proof no longer
   has to manipulate `Psi` values directly.
   The representative side of this input is now checked for every
   `G ∈ L.closing_orientedPatch` by
   `BHWJostOrientedClosedContinuationLoop.exists_initial_final_source_realizations_of_closing`
   and
   `BHWJostOrientedClosedContinuationLoop.exists_initial_final_source_realizations_branch_eqs_of_closing`;
   the unproved part is precisely the source-branch equality supplied by the
   genuine closed-path continuation.  The stronger constructor
   `of_sourcePatch_eqOn` consumes the source-patch form of that same input:
   a source seed where terminal and initial branches agree, together with a
   realization map from the oriented terminal seed into that source seed.  This
   is the closest checked package to the OS I §4.5 continuation proof.  The
   stronger constructor
   `of_closingPatch_sourceBranch_eq` goes one step further: from source-branch
   equality for all matching representatives over `L.closing_orientedPatch`,
   it uses the checked max-rank seed extractor and the closing-patch
   representative helper to produce the terminal-seed package directly.  The
   weaker whole-closing-patch constructor
   `of_closingPatch_exists_sourceBranch_eq` needs only one such matching pair
   for each closing invariant and then performs the same seed extraction.  Its
   method
   `to_finiteOverlapPropagationData` calls the constructor above, its method
   `to_closedLoopSeed` reaches the identity-principle seed layer, its method
   `to_orientedMonodromy_headSliceIFT` gives oriented monodromy on the closing
   patch, its method `to_sourceMonodromy_headSliceIFT` closes the
   source-monodromy goal, and the
   stable public endpoint is
   `BHW.bhw_jost_closedChain_sourceMonodromy_of_closingPatchTerminalSeedData`.
   This is the preferred Lean target for a patch-by-patch accumulated-germ
   Hall-Wightman/Jost proof.

   The ordered finite induction has also been checked:

   ```lean
   theorem BHW.BHWJostOrientedSourcePatchContinuationChain
       .exists_terminalSeed_of_finiteOverlapDomains
       (C : BHW.BHWJostOrientedSourcePatchContinuationChain
         hd n τ Ω0 U B0 p0 z)
       (hn : d + 1 <= n)
       {seed0 : Set (BHW.SourceOrientedGramData d n)}
       (hseed0_rel :
         BHW.IsRelOpenInSourceOrientedGramVariety d n seed0)
       (hseed0_pre : IsPreconnected seed0)
       (hseed0_nonempty : seed0.Nonempty)
       (hseed0_sub_max :
         seed0 ⊆ {G | BHW.SourceOrientedMaxRankAt d n G})
       (D : (j : Fin C.m) -> Set (BHW.SourceOrientedGramData d n))
       (hD_rel :
         ∀ j, BHW.IsRelOpenInSourceOrientedGramVariety d n (D j))
       (hDmax_conn :
         ∀ j, IsConnected
           (D j ∩ {G | BHW.SourceOrientedMaxRankAt d n G}))
       (hD_sub_start :
         ∀ j, D j ⊆ (C.localChart 0).orientedDomain)
       (hD_sub_left :
         ∀ j, D j ⊆ (C.localChart (Fin.castSucc j)).orientedDomain)
       (hT_sub_D :
         ∀ j, (C.oriented_transition j).orientedPatch ⊆ D j)
       (hseed0_sub_D0 :
         ∀ h0 : 0 < C.m, seed0 ⊆ D ⟨0, h0⟩)
       (hT_sub_nextD :
         ∀ (j : Fin C.m) (hnext : j.val + 1 < C.m),
           (C.oriented_transition j).orientedPatch ⊆
             D ⟨j.val + 1, hnext⟩) :
       ∃ terminalSeed : Set (BHW.SourceOrientedGramData d n),
         BHW.IsRelOpenInSourceOrientedGramVariety d n terminalSeed ∧
         IsPreconnected terminalSeed ∧
         terminalSeed.Nonempty ∧
         terminalSeed ⊆ {G | BHW.SourceOrientedMaxRankAt d n G} ∧
         Set.EqOn
           (C.localChart (Fin.last C.m)).Psi
           (C.localChart 0).Psi
           terminalSeed ∧
         (C.m = 0 -> terminalSeed ⊆ seed0) ∧
         (∀ hpos : C.m ≠ 0,
           terminalSeed ⊆
             (C.oriented_transition
               ⟨C.m.pred, Nat.pred_lt hpos⟩).orientedPatch)
   ```

   Its proof is a `Nat` induction on the ordered transition index.  At step
   `j`, it applies `exists_propagatedSeed_to_right` on `D j`; the hypothesis
   `hT_sub_nextD` makes the seed produced in the `j`-th transition patch a
   valid incoming seed for the next domain.  The theorem also exposes the
   terminal seed provenance: for `C.m = 0` the terminal seed remains inside
   `seed0`; for `C.m ≠ 0` it lies inside the last oriented transition patch.
   The helper `BHW.exists_preconnectedRelOpen_maxRankSeed_inside` supplies the
   initial seed from any nonempty relatively open oriented patch in the hard
   range, by choosing a max-rank point and shrinking a full-frame chart inside
   `W ∩ MaxRank`.
   Therefore the hard BHW/Jost theorem no longer has to prove a Lean induction
   principle.  It must now produce: the initial max-rank seed, the ordered
   domains `D j`, the connectedness of each `D j ∩ MaxRank`, the current and
   next containment hypotheses above, and the final closing domain used to build
   `BHWJostOrientedFiniteOverlapPropagationData`.

   The closed-loop producer target is now also checked:

   ```lean
   structure BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       [NeZero d] {hd : 2 <= d} {τ : Equiv.Perm (Fin n)}
       {Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ)}
       {B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ}
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L : BHW.BHWJostOrientedClosedContinuationLoop
         hd n τ Ω0 U B0 p0) where
     hn : d + 1 <= n
     initialSeed : Set (BHW.SourceOrientedGramData d n)
     initialSeed_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n initialSeed
     initialSeed_preconnected : IsPreconnected initialSeed
     initialSeed_nonempty : initialSeed.Nonempty
     initialSeed_sub_max :
       initialSeed ⊆ {G | BHW.SourceOrientedMaxRankAt d n G}
     stepDomain : (j : Fin L.chain.m) ->
       Set (BHW.SourceOrientedGramData d n)
     stepDomain_relOpen :
       ∀ j, BHW.IsRelOpenInSourceOrientedGramVariety d n (stepDomain j)
     stepDomain_maxRank_connected :
       ∀ j, IsConnected
         (stepDomain j ∩ {G | BHW.SourceOrientedMaxRankAt d n G})
     stepDomain_sub_start :
       ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain
     stepDomain_sub_left :
       ∀ j, stepDomain j ⊆
         (L.chain.localChart (Fin.castSucc j)).orientedDomain
     transition_sub_stepDomain :
       ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆
         stepDomain j
     initialSeed_sub_firstDomain :
       ∀ h0 : 0 < L.chain.m, initialSeed ⊆ stepDomain ⟨0, h0⟩
     transition_sub_nextDomain :
       ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
         (L.chain.oriented_transition j).orientedPatch ⊆
           stepDomain ⟨j.val + 1, hnext⟩
     closingDomain : Set (BHW.SourceOrientedGramData d n)
     closingDomain_relOpen :
       BHW.IsRelOpenInSourceOrientedGramVariety d n closingDomain
     closingDomain_maxRank_connected :
       IsConnected
         (closingDomain ∩ {G | BHW.SourceOrientedMaxRankAt d n G})
     closingDomain_sub_final :
       closingDomain ⊆
         (L.chain.localChart (Fin.last L.chain.m)).orientedDomain
     closingDomain_sub_start :
       closingDomain ⊆ (L.chain.localChart 0).orientedDomain
     closingPatch_sub_closingDomain :
       L.closing_orientedPatch ⊆ closingDomain
     closingDomain_contains_initialSeed_of_zero :
       L.chain.m = 0 -> initialSeed ⊆ closingDomain
     closingDomain_contains_lastTransition_of_pos :
       ∀ hpos : L.chain.m ≠ 0,
         (L.chain.oriented_transition
           ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
             closingDomain
   ```

   The checked consumers are:

   ```lean
   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .to_finiteOverlapPropagationData
       (P : BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :
       Nonempty (BHW.BHWJostOrientedFiniteOverlapPropagationData L)

   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .to_closedLoopSeed
       (P : BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L) :
       Nonempty
         (BHW.BHWJostOrientedMaxRankClosedLoopSeed hd n τ Ω0 U B0 L)

   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .to_orientedMonodromy
       (P : BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
       (hclosing_max_conn :
         IsConnected
           (L.closing_orientedPatch ∩
             {G | BHW.SourceOrientedMaxRankAt d n G})) :
       Set.EqOn
         (L.chain.localChart (Fin.last L.chain.m)).Psi
         (L.chain.localChart 0).Psi
         L.closing_orientedPatch

   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .to_sourceMonodromy
       (P : BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
       (hclosing_max_conn :
         IsConnected
           (L.closing_orientedPatch ∩
             {G | BHW.SourceOrientedMaxRankAt d n G})) :
       Set.EqOn
         (L.chain.branch (Fin.last L.chain.m))
         B0
         L.closing_patch
   ```

   Important theorem-shape correction: the following tempting public theorem
   is **not** Lean-ready as an arbitrary-`L` statement:

   ```lean
   theorem BHW.bhw_jost_orientedClosedLoopFiniteOverlapDomainData_of_BHW
       [NeZero d] (hd : 2 <= d) (n : ℕ) (τ : Equiv.Perm (Fin n))
       (Ω0 U : Set (Fin n -> Fin (d + 1) -> ℂ))
       (B0 : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       {p0 : Fin n -> Fin (d + 1) -> ℂ}
       (L : BHW.BHWJostOrientedClosedContinuationLoop
         hd n τ Ω0 U B0 p0)
       (hn : d + 1 <= n) :
       Nonempty
         (BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
   ```

   The checked loop structure by itself does not force every transition
   domain to lie inside the initial oriented chart domain, and it does not
   force the connected max-rank domains required by the propagation theorem.
   Therefore this theorem must not be introduced in production Lean with only
   `L` and `hn` as hypotheses.  The honest remaining producer is the
   source-backed finite-overlap construction for the **specific loops produced
   by the strict OS I §4.5 BHW/Jost atlas**, or equivalently the proof of the
   hypotheses consumed by
   `BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_positivePreconnectedDomains_headSliceIFT`
   and
   `BHWJostOrientedClosedLoopFiniteOverlapDomainData.exists_of_zeroTransitions_closedLoop_headSliceIFT`.
   Once such source-backed domain data is produced for the loop under
   comparison, the old seed theorem is one line: obtain `⟨P⟩` and call
   `P.to_closedLoopSeed`.

   The positive-length data constructor is also checked:

   ```lean
   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .exists_of_positiveDomains
       (hn : d + 1 <= n)
       (hpos : L.chain.m ≠ 0)
       (stepDomain : (j : Fin L.chain.m) ->
         Set (BHW.SourceOrientedGramData d n))
       (stepDomain_relOpen :
         ∀ j, BHW.IsRelOpenInSourceOrientedGramVariety d n (stepDomain j))
       (stepDomain_maxRank_connected :
         ∀ j, IsConnected
           (stepDomain j ∩ {G | BHW.SourceOrientedMaxRankAt d n G}))
       (stepDomain_sub_start :
         ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain)
       (stepDomain_sub_left :
         ∀ j, stepDomain j ⊆
           (L.chain.localChart (Fin.castSucc j)).orientedDomain)
       (transition_sub_stepDomain :
         ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆
           stepDomain j)
       (transition_sub_nextDomain :
         ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
           (L.chain.oriented_transition j).orientedPatch ⊆
             stepDomain ⟨j.val + 1, hnext⟩)
       (closingDomain : Set (BHW.SourceOrientedGramData d n))
       (closingDomain_relOpen :
         BHW.IsRelOpenInSourceOrientedGramVariety d n closingDomain)
       (closingDomain_maxRank_connected :
         IsConnected
           (closingDomain ∩ {G | BHW.SourceOrientedMaxRankAt d n G}))
       (closingDomain_sub_final :
         closingDomain ⊆
           (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
       (closingDomain_sub_start :
         closingDomain ⊆ (L.chain.localChart 0).orientedDomain)
       (closingPatch_sub_closingDomain :
         L.closing_orientedPatch ⊆ closingDomain)
       (closingDomain_contains_lastTransition_of_pos :
         ∀ hpos : L.chain.m ≠ 0,
           (L.chain.oriented_transition
             ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
               closingDomain) :
       Nonempty
         (BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
   ```

   This theorem extracts the initial seed from the first overlap domain using
   `exists_preconnectedRelOpen_maxRankSeed_inside`.  Consequently the
   positive-length BHW/Jost proof now has to produce only the ordered
   nonempty preconnected domains, adjacency containments, and closing domain.

   The checked head-slice IFT consumer is one step closer to the source-normal
   form geometry:

   ```lean
   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .exists_of_positivePreconnectedDomains_headSliceIFT
       (hn : d + 1 <= n)
       (hpos : L.chain.m ≠ 0)
       (stepDomain : (j : Fin L.chain.m) ->
         Set (BHW.SourceOrientedGramData d n))
       (stepDomain_relOpen :
         ∀ j, BHW.IsRelOpenInSourceOrientedGramVariety d n (stepDomain j))
       (stepDomain_preconnected :
         ∀ j, IsPreconnected (stepDomain j))
       (stepDomain_nonempty :
         ∀ j, (stepDomain j).Nonempty)
       (stepDomain_sub_start :
         ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain)
       (stepDomain_sub_left :
         ∀ j, stepDomain j ⊆
           (L.chain.localChart (Fin.castSucc j)).orientedDomain)
       (transition_sub_stepDomain :
         ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆
           stepDomain j)
       (transition_sub_nextDomain :
         ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
           (L.chain.oriented_transition j).orientedPatch ⊆
             stepDomain ⟨j.val + 1, hnext⟩)
       (closingDomain : Set (BHW.SourceOrientedGramData d n))
       (closingDomain_relOpen :
         BHW.IsRelOpenInSourceOrientedGramVariety d n closingDomain)
       (closingDomain_preconnected : IsPreconnected closingDomain)
       (closingDomain_nonempty : closingDomain.Nonempty)
       (closingDomain_sub_final :
         closingDomain ⊆
           (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
       (closingDomain_sub_start :
         closingDomain ⊆ (L.chain.localChart 0).orientedDomain)
       (closingPatch_sub_closingDomain :
         L.closing_orientedPatch ⊆ closingDomain)
       (closingDomain_contains_lastTransition_of_pos :
         ∀ hpos : L.chain.m ≠ 0,
           (L.chain.oriented_transition
             ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
               closingDomain) :
       Nonempty
         (BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
   ```

   This is the producer-facing target.  A source-normal-form shrink normally
   gives a relatively open preconnected image patch with an explicit source
   representative, not an already massaged max-rank-connected stratum.  The
   theorem converts nonempty plus preconnected to `IsConnected` and then calls
   `sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT`.
   Thus the remaining positive-length finite-overlap proof is exactly the
   ordered-overlap geometry and containment transcript; it no longer includes
   exceptional-rank local-image bookkeeping.

   The zero-transition closed-loop edge case is already checked:

   ```lean
   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .exists_of_zeroTransitions
       (hn : d + 1 <= n)
       (hm : L.chain.m = 0)
       (hclosing_max_connected :
         IsConnected
           (L.closing_orientedPatch ∩
             {G | BHW.SourceOrientedMaxRankAt d n G})) :
       Nonempty
         (BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
   ```

   It extracts the initial seed directly inside `L.closing_orientedPatch` and
   uses the closing patch as the closing domain.  Thus the remaining positive
   work is the nonzero finite-overlap geometry.

   The even more concrete checked zero-transition endpoint is:

   ```lean
   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .exists_of_zeroTransitions_closedLoop_headSliceIFT
       (hn : d + 1 <= n)
       (hm : L.chain.m = 0) :
       Nonempty
         (BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
   ```

   It uses the stored `L.closing_orientedPatch_preconnected` and
   `L.closing_orientedPatch_nonempty`, then applies the same checked
   head-slice IFT max-rank connectedness theorem.  So a zero-step loop has no
   remaining Hall-Wightman/Jost geometric obligation.

   The low-level constructor behind the producer-facing package is:

   ```lean
   theorem BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData
       .exists_of_preconnectedDomains_headSliceIFT
       (hn : d + 1 <= n)
       (stepDomain : (j : Fin L.chain.m) ->
         Set (BHW.SourceOrientedGramData d n))
       (stepDomain_relOpen :
         ∀ j, BHW.IsRelOpenInSourceOrientedGramVariety d n (stepDomain j))
       (stepDomain_preconnected :
         ∀ j, IsPreconnected (stepDomain j))
       (stepDomain_nonempty :
         ∀ j, (stepDomain j).Nonempty)
       (stepDomain_sub_start :
         ∀ j, stepDomain j ⊆ (L.chain.localChart 0).orientedDomain)
       (stepDomain_sub_left :
         ∀ j, stepDomain j ⊆
           (L.chain.localChart (Fin.castSucc j)).orientedDomain)
       (transition_sub_stepDomain :
         ∀ j, (L.chain.oriented_transition j).orientedPatch ⊆
           stepDomain j)
       (transition_sub_nextDomain :
         ∀ (j : Fin L.chain.m) (hnext : j.val + 1 < L.chain.m),
           (L.chain.oriented_transition j).orientedPatch ⊆
             stepDomain ⟨j.val + 1, hnext⟩)
       (closingDomain : Set (BHW.SourceOrientedGramData d n))
       (closingDomain_relOpen :
         BHW.IsRelOpenInSourceOrientedGramVariety d n closingDomain)
       (closingDomain_preconnected : IsPreconnected closingDomain)
       (closingDomain_nonempty : closingDomain.Nonempty)
       (closingDomain_sub_final :
         closingDomain ⊆
           (L.chain.localChart (Fin.last L.chain.m)).orientedDomain)
       (closingDomain_sub_start :
         closingDomain ⊆ (L.chain.localChart 0).orientedDomain)
       (closingPatch_sub_closingDomain :
         L.closing_orientedPatch ⊆ closingDomain)
       (closingDomain_contains_lastTransition_of_pos :
         ∀ hpos : L.chain.m ≠ 0,
           (L.chain.oriented_transition
             ⟨L.chain.m.pred, Nat.pred_lt hpos⟩).orientedPatch ⊆
               closingDomain) :
       Nonempty
         (BHW.BHWJostOrientedClosedLoopFiniteOverlapDomainData L)
   ```

   Its proof is only a `by_cases hm : L.chain.m = 0`: the zero branch calls
   `exists_of_zeroTransitions_closedLoop_headSliceIFT`, and the positive
   branch calls `exists_of_positivePreconnectedDomains_headSliceIFT`.

   In production code, the future strict source-backed BHW/Jost theorem should
   prefer returning
   `BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L` rather
   than passing this long argument list directly.  That package is the exact
   Lean boundary: the source-backed construction proves the ordered
   relatively open nonempty preconnected domains and containment transcript;
   the checked consumer converts it to monodromy.
   However, this package is still a strong source-backed input, not a theorem
   about arbitrary chart loops: the fields
   `stepDomain_sub_start : ∀ j, stepDomain j ⊆
   (L.chain.localChart 0).orientedDomain` and
   `closingDomain_sub_start` are what make
   `Φ := (L.chain.localChart 0).Psi` holomorphic on every finite-overlap
   domain.  If the strict OS I §4.5 construction cannot provide a starting
   oriented domain covering the whole positive-length ribbon, the correct
   Lean replacement is an accumulated-germ continuation chain whose step `j`
   carries a branch already constructed on the current domain and compares it
   to the next branch on the next overlap.  The current checked consumer is
   sound only as a conditional consumer of the large-start-domain data.
   The zero-transition case of this package is already discharged:
   `BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData.exists_of_zeroTransitions`
   fills the empty step family by `Fin.elim0`, chooses
   `L.closing_orientedPatch` as `closingDomain`, and the public theorem
   `BHW.bhw_jost_closedChain_sourceMonodromy_of_zeroTransitions` immediately
   gives source monodromy.  Therefore the only remaining finite-overlap
   producer content is the positive-length ordered ribbon.

   Once `P :
   BHWJostOrientedClosedLoopPreconnectedFiniteOverlapDomainData L` is
   available, no extra closing-patch max-rank connectedness input remains.
   The checked consumers `P.to_orientedMonodromy_headSliceIFT` and
   `P.to_sourceMonodromy_headSliceIFT` derive
   `IsConnected (L.closing_orientedPatch ∩ MaxRank)` from the stored
   nonempty/preconnected closing patch and
   `sourceOrientedGramVariety_maxRank_inter_relOpen_isConnected_of_headSliceIFT`,
   then call the existing monodromy consumers.  The public endpoint theorem is
   `BHW.bhw_jost_closedChain_sourceMonodromy_of_preconnectedFiniteOverlapData`,
   so the future BHW/Jost producer therefore ends with:

   ```lean
   exact
     BHW.bhw_jost_closedChain_sourceMonodromy_of_preconnectedFiniteOverlapData P
   ```

   `BHWJostOrientedTransitionData.propagate_eqOn_to_right_maxRank` is the
   checked one-step version.  Given an accumulated oriented germ `Φ`, a
   transition `T : Cleft -> Cright`, a relatively open intermediate domain
   `D ⊆ Cleft.orientedDomain` whose max-rank part is connected, and a
   nonempty relatively open seed inside `D ∩ MaxRank` where `Φ = Cleft.Psi`,
   the hard-range identity theorem
   `sourceOrientedGramVariety_maxRank_eqOn_of_connected_fullFrame` gives
   `Φ = Cleft.Psi` on `D ∩ MaxRank`.  On
   `T.orientedPatch ∩ MaxRank`, the hypothesis `T.orientedPatch ⊆ D` lets us
   restrict this equality and then compose it with the stored transition
   equality `T.oriented_psi_agree : Cleft.Psi = Cright.Psi`.  The conclusion
   is exactly `Φ = Cright.Psi` on the max-rank part of the next transition
   patch.

   `exists_maxRankSeed_eqOn_of_connected_domain` is the generic target-patch
   form used by both transition propagation and the final closing-overlap
   propagation.  First apply
   `sourceOrientedGramVariety_maxRank_eqOn_of_connected_fullFrame` on `D` to
   extend equality from the old seed to `D ∩ MaxRank`; then prove
   `W ∩ MaxRank` is relatively open and nonempty, choose a max-rank center,
   build the full-frame finite-coordinate chart there, shrink it by
   `connectedMaxRankPatch_inside_relOpen`, and restrict the equality to the
   resulting preconnected seed.

   `BHWJostOrientedMaxRankClosedLoopSeed.exists_of_connectedDomainPropagation`
   is the checked closing-overlap package theorem.  If the propagated equality
   between the terminal and initial oriented germs has reached a nonempty
   max-rank seed inside a relatively open domain `D`, if `D ∩ MaxRank` is
   connected, and if `D` contains the closing oriented patch while lying inside
   both the terminal and initial chart oriented domains, then the generic
   target-patch theorem with `W := L.closing_orientedPatch` produces a fresh
   nonempty preconnected relatively open max-rank seed inside the closing
   patch.  The theorem packages that seed as
   `BHWJostOrientedMaxRankClosedLoopSeed`.  Thus the finite-overlap proof no
   longer has to manipulate the closed-loop seed fields directly.

   `exists_propagatedSeed_to_right` composes this equality theorem with the
   checked max-rank seed extractor
   `SourceOrientedMaxRankChartData.connectedMaxRankPatch_inside_relOpen`.
   It first proves that
   `T.orientedPatch ∩ {G | SourceOrientedMaxRankAt d n G}` is relatively open
   and nonempty by
   `sourceOrientedRelOpen_inter_maxRank_relOpen` and
   `sourceOrientedRelOpen_inter_maxRank_nonempty`, chooses a max-rank center,
   builds the finite-coordinate full-frame chart at that center using
   `sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame`, shrinks that chart
   to a connected relatively open patch inside the transition max-rank set,
   and restricts the equality from `propagate_eqOn_to_right_maxRank` to this
   patch.  The result has exactly the rel-open/preconnected/nonempty/max-rank
   shape needed for the next finite-overlap propagation step.

   `bhw_continuedValueAlongOrientedChain` is now only the endpoint projection
   of a chain that already carries its recursively constructed local branches.
   The producer of `BHWJostOrientedSourcePatchContinuationChain` is where the
   strict-route recursion lives:
   the base point is the fixed `p0` selected from `Ω0 ∩ U`, and the stored
   `start_patch` is an open preconnected neighborhood with
   `p0 ∈ start_patch ⊆ Ω0 ∩ C.chart 0`.  On `C.chart 0`, define the first
   local branch by the local BHW/Jost continuation theorem applied to `B0` and
   normalize it so it agrees with `B0` on that start patch.
   Inductively, suppose `C.branch j` is holomorphic on `C.chart j`.  Choose
   an open preconnected patch
   `Pj ⊆ C.chart j ∩ C.chart j.succ`; define `C.branch j.succ` on the next
   chart by the same local continuation, normalized to agree with
   `C.branch j` on `Pj`.  The identity theorem on `Pj` proves independence of
   the selected patch and gives the stored `consecutive_agree` field.
   Therefore

   ```lean
   BHW.bhw_continuedValueAlongOrientedChain hd n τ Ω0 U B0 C =
     C.branch (Fin.last C.m) z
   ```

   with `C.final_mem : z ∈ C.chart (Fin.last C.m)`.  Single-valuedness on the
   strict route is not proved by naively traversing `C₁` and then the stored
   reverse of `C₂`; that construction needs a terminal bridge which is the
   desired conclusion.  The Lean-ready comparison instead carries transfer
   provenance, proves one-step Hall-Wightman uniqueness for two descents from
   equal previous germs, and applies the closed-path source monodromy theorem
   only to the source-backed return trace.  The resulting base-patch equality
   is then transported along the second trace by the finite uniqueness
   induction, producing the endpoint patch as output.  Holomorphy of the
   assembled global branch on `U` is local: around `z`, use the final chart of
   a chosen trace to define the branch; on overlaps of two such neighborhoods,
   the trace single-valuedness theorem identifies the two local definitions.
   The atlas
   also includes the explicit restricted `Ω0 ∩ U`/`B0` chart, so base
   agreement is a special case of the same comparison rather than a separate
   hidden assumption.

   The ordinary and adjacent branch producers are then:

   ```lean
   theorem BHW.os45_sourcePatch_ordinaryBranch_onHull_figure24SourcePatch
       [NeZero d] (hd : 2 <= d)
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
       (H : BHW.OS45SourcePatchBHWJostHullData hd OS lgc n i hi
         (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)) :
       ∃ Bord : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ,
         DifferentiableOn ℂ Bord H.U ∧
         (∀ x, x ∈ BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ->
           Bord (fun k => wickRotatePoint (x k)) =
             bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
         (∀ x, x ∈ BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ->
           Bord (BHW.realEmbed x) =
             BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x))

   theorem BHW.os45_sourcePatch_adjacentBranch_onHull_figure24SourcePatch_of_OSI45
       [NeZero d] (hd : 2 <= d)
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
       (H : BHW.OS45SourcePatchBHWJostHullData hd OS lgc n i hi
         (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)) :
       ∃ Btau : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ,
         DifferentiableOn ℂ Btau H.U ∧
         (∀ x, x ∈ BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ->
           Btau (fun k => wickRotatePoint (x k)) =
             bvt_F OS lgc n (fun k => wickRotatePoint (x (H.τ k)))) ∧
         (∀ x, x ∈ BHW.os45Figure24SourcePatch (d := d) (n := n) i hi ->
           Btau (BHW.realEmbed x) =
             BHW.extendF (bvt_F OS lgc n)
               (BHW.realEmbed (fun k => x (H.τ k))))
   ```

   The ordinary proof applies the local BHW continuation theorem with
   `Ω0 := BHW.ExtendedTube d n`, `B0 := BHW.extendF (bvt_F OS lgc n)`, and
   traces supplied by `BHW.extendF_eq_on_forwardTube` and the continuation
   agreement field on `H.real_id_ET`.  Its continuation-theorem inputs are now
   checked accessors: `H.U_hull`, `H.U_isPathConnected`,
   `H.extendedTube_subset_ambient`, and `H.extendedTube_meets_U`.  The
   adjacent proof applies the same theorem
   with `Ω0 := {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}` and
   `B0 z := BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) H.τ z)`.
   Holomorphy is `BHW.extendF_holomorphicOn.comp` with the continuous linear
   permutation map.  Its continuation-theorem inputs are
   `H.U_hull`, `H.U_isPathConnected`,
   `H.adjacentExtendedTubePreimage_subset_ambient`, and
   `H.adjacentExtendedTubePreimage_meets_U`; open-domain and initial
   holomorphy inputs are the checked
   `BHW.isOpen_permAct_preimage_extendedTube` and
   `BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube`.
   The ordinary initial holomorphy input is the checked
   `BHW.differentiableOn_extendF_bvt_F_extendedTube`.  The real trace rewrite
   uses `BHW.permAct_realEmbed` and `H.real_tau_ET`; the adjacent Wick trace is
   not obtained from a direct
   `H.wick_tau_ET` field, but from the OS-I/BHW continuation datum that
   transports the adjacent ordered Wick boundary formula to the selected hull.
   The OS-I input is exactly this covariance/branch-selection used to justify
   the local BHW continuation; no later common-boundary or Jost/Ruelle
   uniqueness theorem is involved.

   The checked strict-route consumer for these two branch producers is now
   `BHW.OS45SourcePatchBHWJostOrientedContinuationInputs.exists_gluedBranch`
   in `OSToWightmanLocalityOS45BHWJostContinuation.lean`.  It is a thin
   specialization of the already checked
   `BHW.bhw_jost_orientedGluedBranch_of_pathConnected_sourceNormalFormProducer_retargetedComparisons`
   and therefore exposes the honest remaining analytic inputs rather than
   hiding them: `patchAt`, `uniformDescent`, `uniformDescent_unique`,
   `retargetedComparison`, the initial oriented chart `C0`, the start patch,
   and the initial-chart agreement on `Ω0 ∩ H.U`.  The checked
   `H.exists_ordinaryBranch_of_orientedContinuationInputs` then supplies the
   ordinary branch, holomorphy on `H.U`, Wick trace by
   `BHW.extendF_bvt_F_wickRotate_eq_of_ordered`, and real trace by
   continuation agreement.  The checked
   `H.exists_adjacentBranch_of_orientedContinuationInputs` supplies the
   adjacent branch, holomorphy on `H.U`, real trace by `BHW.permAct_realEmbed`,
   and initial-domain agreement on the permutation preimage of
   `ExtendedTube`; its Wick trace remains a separate OS I/BHW continuation
   datum.  The checked
   `H.pairDataOfOrientedContinuationInputs` chooses the two branches from
   those input packets and calls
   `BHW.OS45SourcePatchBHWJostPairData.ofHullDataAndBranches`; therefore the
   exact remaining inputs to build the pair carrier are just the ordinary
   strict-oriented continuation packet, the adjacent strict-oriented
   continuation packet, and the adjacent Wick trace formula on the selected
   source patch.

   With these three surfaces,
   `BHW.os45_sourcePatch_bhwJostPairData_on_figure24SourcePatch_of_OSI45`
   has a field-by-field Lean body: build `H` on
   `BHW.os45Figure24SourcePatch`, obtain `Bord` and `Btau`, and call the
   checked constructor
   `BHW.OS45SourcePatchBHWJostPairData.ofHullDataAndBranches`.  This
   constructor copies `H.τ`, `H.U`, `H.V_open`, `H.V_nonempty`, `H.U_open`,
   `H.U_connected`, `H.wick_id_mem`, `H.real_id_mem`, and stores the two
   branches plus their four trace fields.  The pair-data theorem itself then
   contains no hidden analytic step.

   Production Lean has already replaced the separate difference carrier by
   methods on the checked pair carrier:

   ```lean
   def BHW.OS45SourcePatchBHWJostPairData.difference
       (P : BHW.OS45SourcePatchBHWJostPairData
         (d := d) hd OS lgc n i hi V) :
       (Fin n -> Fin (d + 1) -> ℂ) -> ℂ :=
     fun z => P.Btau z - P.Bord z

   theorem BHW.OS45SourcePatchBHWJostPairData.difference_holo
       (P : BHW.OS45SourcePatchBHWJostPairData
         (d := d) hd OS lgc n i hi V) :
       DifferentiableOn ℂ P.difference P.U

   theorem BHW.OS45SourcePatchBHWJostPairData.difference_wick_trace
       (P : BHW.OS45SourcePatchBHWJostPairData
         (d := d) hd OS lgc n i hi V)
       {x : NPointDomain d n} (hx : x ∈ V) :
       P.difference (fun k => wickRotatePoint (x k)) =
         bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) -
           bvt_F OS lgc n (fun k => wickRotatePoint (x k))

   theorem BHW.OS45SourcePatchBHWJostPairData.difference_real_trace
       (P : BHW.OS45SourcePatchBHWJostPairData
         (d := d) hd OS lgc n i hi V)
       {x : NPointDomain d n} (hx : x ∈ V) :
       P.difference (BHW.realEmbed x) =
         BHW.extendF (bvt_F OS lgc n)
             (BHW.realEmbed (fun k => x (P.τ k))) -
           BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
   ```

   Therefore the next Lean producer must return the checked pair carrier
   itself, not an auxiliary `DifferenceData` wrapper.  The first active target
   is the exact-source-patch theorem displayed above:
   `BHW.os45_sourcePatch_bhwJostPairData_on_figure24SourcePatch_of_OSI45 ... :
   BHW.OS45SourcePatchBHWJostPairData hd OS lgc n i hi
     (BHW.os45Figure24SourcePatch (d := d) (n := n) i hi)`.
   Any chart-local version is a later restriction corollary using
   `BHW.OS45SourcePatchBHWJostPairData.restrict`, not an analytic producer.
   The producer must not use the oriented common-boundary envelope or the
   oriented branch-germ suppliers.

3. Boundary uniqueness on this direct carrier.  The zero Wick distribution
   from item 1 is converted first to pointwise zero of the checked
   `P.difference` on the BHW/Jost hull, then to the `hzero` input consumed by
   the checked algebra.  The missing topology is explicit: `P.V_open`,
   `P.V_nonempty`, the standard real-linear Wick embedding
   `x ↦ fun k => wickRotatePoint (x k)`, and `P.wick_mem` make the Wick trace
   of `V` a nonempty open totally-real slice in `P.U`.

   ```lean
   theorem BHW.os45_pairData_difference_identity_of_wickDistributionZero
       [NeZero d] (hd : 2 <= d)
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
       (V : Set (NPointDomain d n))
       (P : BHW.OS45SourcePatchBHWJostPairData hd OS lgc n i hi V)
       (hwick_zero :
         ∀ χ : SchwartzNPoint d n,
           HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
           tsupport (χ : NPointDomain d n -> ℂ) ⊆ V ->
           ∫ x : NPointDomain d n,
             (bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) -
               bvt_F OS lgc n (fun k => wickRotatePoint (x k))) * χ x = 0) :
       ∀ z ∈ P.U, P.difference z = 0
   ```

   Proof transcript: first apply
   `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` to
   the continuous function
   `x ↦ P.difference (fun k => wickRotatePoint (x k))` on the open set `V`;
   continuity is `P.difference_holo.continuousOn.comp` with `P.wick_mem`, and
   the compact-test integral is rewritten by `P.difference_wick_trace` and
   `hwick_zero`.  Then apply the standard product totally-real identity
   theorem to the holomorphic function `P.difference` on the connected open
   set `P.U`, using `P.V_nonempty` and the
   fact that the Wick embedding is a complexification chart for the real
   coordinates.  This is an OS-free SCV/totally-real lemma specialized to the
   direct carrier; it does not use the oriented common-boundary envelope.

   The real-trace/distribution theorem is then the exact `hzero` shape needed
   by the checked consumer:

   ```lean
   theorem BHW.os45_pairData_difference_realTrace_zero_of_wickDistributionZero
       [NeZero d] (hd : 2 <= d)
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
       (V : Set (NPointDomain d n))
       (P : BHW.OS45SourcePatchBHWJostPairData hd OS lgc n i hi V)
       (hwick_zero :
         ∀ χ : SchwartzNPoint d n,
           HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
           tsupport (χ : NPointDomain d n -> ℂ) ⊆ V ->
           ∫ x : NPointDomain d n,
             (bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) -
               bvt_F OS lgc n (fun k => wickRotatePoint (x k))) * χ x = 0)
       (ψ : SchwartzNPoint d n) :
       HasCompactSupport (ψ : NPointDomain d n -> ℂ) ->
       tsupport (ψ : NPointDomain d n -> ℂ) ⊆ V ->
       ∫ x : NPointDomain d n,
           P.difference (BHW.realEmbed x) * ψ x = 0
   ```

   Its proof calls
   `BHW.os45_pairData_difference_identity_of_wickDistributionZero`, rewrites
   the integrand to zero on `V`, and uses compact support of `ψ` to make the
   integrand zero off `V`.  The checked theorem
   `BHW.realSourceBranchDifference_zero_of_pairData_difference_zero` then
   translates this `P.difference` zero into the explicit `extendF` real-source
   branch-difference zero.  This item is an edge/totally-real uniqueness lemma
   for a holomorphic branch-difference carrier, not the final Jost p. 83
   locality theorem.  It must not mention `bvt_W` locality or the later
   oriented branch-germ envelope.

4. Public source-patch assembly.  The public theorem only combines items 1--3
   and rewrites `∫ (Aτ - A) * ψ = 0` into the displayed equality of source
   pairings.  The bookkeeping lemma is:

   ```lean
   theorem BHW.integral_realSourceBranchDifference_eq_zero_to_pairing_eq
       [NeZero d]
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (τ : Equiv.Perm (Fin n))
       (ψ : SchwartzNPoint d n)
       (hid_int :
         Integrable
           (fun x : NPointDomain d n =>
             BHW.extendF (bvt_F OS lgc n)
               (BHW.realEmbed x) * ψ x))
       (hτ_int :
         Integrable
           (fun x : NPointDomain d n =>
             BHW.extendF (bvt_F OS lgc n)
               (BHW.realEmbed (fun k => x (τ k))) * ψ x))
       (hzero :
         ∫ x : NPointDomain d n,
             (BHW.extendF (bvt_F OS lgc n)
                 (BHW.realEmbed (fun k => x (τ k))) -
               BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) * ψ x = 0) :
       ∫ x : NPointDomain d n,
           BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * ψ x
         =
       ∫ x : NPointDomain d n,
           BHW.extendF (bvt_F OS lgc n)
             (BHW.realEmbed (fun k => x (τ k))) * ψ x := by
     have hdiff :
         (∫ x : NPointDomain d n,
             BHW.extendF (bvt_F OS lgc n)
               (BHW.realEmbed (fun k => x (τ k))) * ψ x) -
         (∫ x : NPointDomain d n,
             BHW.extendF (bvt_F OS lgc n)
               (BHW.realEmbed x) * ψ x) = 0 := by
       simpa [sub_mul] using
         (by
           rw [MeasureTheory.integral_sub hτ_int hid_int]
           exact hzero)
     exact (sub_eq_zero.mp hdiff).symm
   ```

   The Wick-side integrability hypotheses for the checked Euclidean-edge
   bridge are now checked below.  The identity Wick trace is continuous on the
   ordered real source patch by `bvt_F_holomorphic`,
   `BHW.continuous_wickRotateRealConfig`, and
   `wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector`; compact
   support then gives integrability by
   `SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen`.  A permuted
   Wick trace is reduced pointwise to the identity Wick trace by the checked
   global permutation invariance `bvt_F_perm`.  Thus no separate unproved
   source-chart growth theorem is hidden here.

   ```lean
   theorem BHW.continuous_wickRotateRealConfig
       {d n : Nat} :
       Continuous
         (fun x : NPointDomain d n => fun k => wickRotatePoint (x k))

   theorem BHW.integrable_bvt_F_wickRotate_mul_schwartz_of_orderedSector
       [NeZero d]
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat)
       (V : Set (NPointDomain d n))
       (hV_open : IsOpen V)
       (hV_ordered :
         ∀ x, x ∈ V ->
           x ∈ EuclideanOrderedPositiveTimeSector
             (d := d) (n := n) (1 : Equiv.Perm (Fin n)))
       (φ : SchwartzNPoint d n)
       (hφ_comp : HasCompactSupport (φ : NPointDomain d n -> ℂ))
       (hφ_supp : tsupport (φ : NPointDomain d n -> ℂ) ⊆ V) :
       Integrable
         (fun u : NPointDomain d n =>
           bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u)

   theorem BHW.integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector
       [NeZero d]
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat)
       (V : Set (NPointDomain d n))
       (hV_open : IsOpen V)
       (hV_ordered :
         ∀ x, x ∈ V ->
           x ∈ EuclideanOrderedPositiveTimeSector
             (d := d) (n := n) (1 : Equiv.Perm (Fin n)))
       (ρ : Equiv.Perm (Fin n))
       (φ : SchwartzNPoint d n)
       (hφ_comp : HasCompactSupport (φ : NPointDomain d n -> ℂ))
       (hφ_supp : tsupport (φ : NPointDomain d n -> ℂ) ⊆ V) :
       Integrable
         (fun u : NPointDomain d n =>
           bvt_F OS lgc n
             (fun k => wickRotatePoint (u (ρ k))) * φ u)
   ```

   The public source-patch theorem is then Lean-mechanical:

   ```lean
   theorem BHW.integrable_extendF_realSource_mul_schwartz_of_ET
       [NeZero d]
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat)
       (V : Set (NPointDomain d n))
       (hV_open : IsOpen V)
       (ρ : Equiv.Perm (Fin n))
       (hVρ_ET :
         ∀ x, x ∈ V ->
           BHW.realEmbed (fun k => x (ρ k)) ∈ BHW.ExtendedTube d n)
       (φ : SchwartzNPoint d n)
       (hφ_comp : HasCompactSupport (φ : NPointDomain d n -> ℂ))
       (hφ_supp : tsupport (φ : NPointDomain d n -> ℂ) ⊆ V) :
       Integrable
         (fun u : NPointDomain d n =>
           BHW.extendF (bvt_F OS lgc n)
             (BHW.realEmbed (fun k => u (ρ k))) * φ u)

   theorem BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45
       [NeZero d] (hd : 2 <= d)
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
       (V : Set (NPointDomain d n))
       (hV_open : IsOpen V)
       (hV_jost : ∀ x, x ∈ V -> x ∈ BHW.JostSet d n)
       (hV_ET : ∀ x, x ∈ V -> BHW.realEmbed x ∈ BHW.ExtendedTube d n)
       (hV_swapET :
         ∀ x, x ∈ V ->
           BHW.realEmbed
             (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           BHW.ExtendedTube d n)
       (hV_ordered :
         ∀ x, x ∈ V ->
           x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) 1)
       (hV_swap_ordered :
         ∀ x, x ∈ V ->
           (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
             EuclideanOrderedPositiveTimeSector (d := d) (n := n)
               (Equiv.swap i ⟨i.val + 1, hi⟩))
       (hV_adjLift_ET :
         let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
         ∀ x, x ∈ V -> ∀ t,
           BHW.os45Figure24AdjacentLift (d := d) (n := n) hd τ x t ∈
           BHW.ExtendedTube d n)
       (hV_sourcePatch :
         V ⊆ BHW.os45Figure24SourcePatch (d := d) n i hi)
       {x0 : NPointDomain d n}
       (hx0V : x0 ∈ V)
       (hChart : BHW.OS45Figure24SourceChartAt hd OS lgc n i hi V x0)
       (hV_orientedPath_closure :
         ∀ x ∈ closure hChart.V0,
           BHW.OS45Figure24OrientedPathField (d := d) n i hi x)
       (ψ : SchwartzNPoint d n)
       (hψ_comp : HasCompactSupport (ψ : NPointDomain d n -> ℂ))
       (hψ_supp : tsupport (ψ : NPointDomain d n -> ℂ) ⊆ hChart.V0) :
       ∫ u : NPointDomain d n,
           BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u) * ψ u
         =
       ∫ u : NPointDomain d n,
           BHW.extendF (bvt_F OS lgc n)
             (BHW.realEmbed
               (fun k => u (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * ψ u := by
     classical
     let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
     have hwickτ_int :
         ∀ χ : SchwartzNPoint d n,
           HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
           tsupport (χ : NPointDomain d n -> ℂ) ⊆ hChart.V0 ->
           Integrable
             (fun x : NPointDomain d n =>
               bvt_F OS lgc n
                 (fun k => wickRotatePoint (x (τ k))) * χ x) :=
       BHW.integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector
         (d := d) OS lgc n hChart.V0 hChart.V0_open
         (fun x hx => hV_ordered x (hChart.V0_sub hx)) τ
     have hwickid_int :
         ∀ χ : SchwartzNPoint d n,
           HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
           tsupport (χ : NPointDomain d n -> ℂ) ⊆ hChart.V0 ->
           Integrable
             (fun x : NPointDomain d n =>
               bvt_F OS lgc n
                 (fun k => wickRotatePoint (x k)) * χ x) :=
       BHW.integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector
         (d := d) OS lgc n hChart.V0 hChart.V0_open
         (fun x hx => hV_ordered x (hChart.V0_sub hx))
         (1 : Equiv.Perm (Fin n))
     have hwick_zero :=
       BHW.os45_wickBranchDifference_zero_of_euclideanEdge_pairing_eq_on_timeSector
         (d := d) OS lgc n i hi hChart.V0
         (fun x hx => hV_jost x (hChart.V0_sub hx))
         (1 : Equiv.Perm (Fin n))
         (fun x hx => hV_ordered x (hChart.V0_sub hx))
         (fun x hx => by
           simpa [τ, Equiv.swap_inv, one_mul] using
             hV_swap_ordered x (hChart.V0_sub hx))
         hwickτ_int hwickid_int
     let Pfull :=
       BHW.os45_sourcePatch_bhwJostPairData_on_figure24SourcePatch_of_OSI45
         (d := d) hd OS lgc n i hi
     let P :=
       Pfull.restrict hChart.V0 hChart.V0_open
         ⟨x0, hChart.x0_mem⟩
         (fun x hx => hV_sourcePatch (hChart.V0_sub hx))
     have hwick_zero_P :
         ∀ χ : SchwartzNPoint d n,
           HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
           tsupport (χ : NPointDomain d n -> ℂ) ⊆ hChart.V0 ->
           ∫ x : NPointDomain d n,
             (bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) -
               bvt_F OS lgc n (fun k => wickRotatePoint (x k))) * χ x = 0 := by
       intro χ hχ_comp hχ_supp
       simpa [P.τ_eq] using hwick_zero χ hχ_comp hχ_supp
     have hzero_P :
         ∀ χ : SchwartzNPoint d n,
           HasCompactSupport (χ : NPointDomain d n -> ℂ) ->
           tsupport (χ : NPointDomain d n -> ℂ) ⊆ hChart.V0 ->
           ∫ x : NPointDomain d n,
             P.difference (BHW.realEmbed x) * χ x = 0 :=
       BHW.os45_pairData_difference_realTrace_zero_of_wickDistributionZero
         (d := d) hd OS lgc n i hi hChart.V0 P hwick_zero_P
     have hreal_zero :=
       BHW.realSourceBranchDifference_zero_of_pairData_difference_zero
         (d := d) (n := n) P hzero_P ψ hψ_comp hψ_supp
     have hid_int :=
       BHW.integrable_extendF_realSource_mul_schwartz_of_ET
         (d := d) OS lgc n hChart.V0 hChart.V0_open
         (1 : Equiv.Perm (Fin n))
         (fun x hx => by
           simpa using hV_ET x (hChart.V0_sub hx))
         ψ hψ_comp hψ_supp
     have hτ_int :=
       BHW.integrable_extendF_realSource_mul_schwartz_of_ET
         (d := d) OS lgc n hChart.V0 hChart.V0_open P.τ
         (fun x hx => by
           simpa [P.τ_eq] using hV_swapET x (hChart.V0_sub hx))
         ψ hψ_comp hψ_supp
     have hpair :=
       BHW.integral_realSourceBranchDifference_eq_zero_to_pairing_eq
         (d := d) OS lgc n P.τ ψ hid_int hτ_int hreal_zero
     simpa [P.τ_eq] using hpair
   ```

   The real-source integrability helper is now checked.  It composes
   `BHW.extendF_holomorphicOn` for `BHW.extendF (bvt_F OS lgc n)` with the
   continuous real-embedding/permutation map, takes the appropriate
   extended-tube membership hypothesis as `hVρ_ET`, then applies
   `SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen`.  The argument
   uses `hV_adjLift_ET` and `hV_orientedPath_closure` only to
   keep the source-chart input compatible with downstream Figure-2-4
   consumers; the direct carrier itself is not allowed to call the oriented
   branch-germ suppliers.  Together with the Wick-edge integrability helper
   above, this last step is measure algebra plus `sub_eq_zero`, not a new
   analytic theorem.

The exact checked Euclidean edge theorem is:

```lean
theorem os45_adjacent_euclideanEdge_pairing_eq_on_timeSector
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : Nat) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (ρ : Equiv.Perm (Fin n))
    (_hV_ordered : ∀ x ∈ V,
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (_hV_swap_ordered : ∀ x ∈ V,
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
    (φ : SchwartzNPoint d n)
    (hφ_tsupport :
      tsupport (φ : NPointDomain d n -> ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (fun k =>
            wickRotatePoint (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
      =
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x
```

Thus the source-pairing proof must call it with `ρ := 1`, with the support
proof restricted to the selected `V0`, and with the swapped ordered-sector
field normalized from `τ` to `(Equiv.swap i ⟨i.val + 1, hi⟩).symm * 1` by
`Equiv.swap_inv` and `mul_one`.  It does not take `hd`, `hV_open`, or a
separate compact-support hypothesis.  If a downstream public theorem needs
the same finite permutation change of variables, use the public
`integral_perm_eq_self` from `WickRotation/SchwingerAxioms.lean`; do not
reach for the private helper `integral_perm_eq_self_locality`.

The adjacent branch producer must expose the OS-I §4.5 chain explicitly.  Its
proof first fixes the zero-diagonal orientation
`φZ`, `ψZ := permuteZeroDiagonalSchwartz τ.symm φZ`, with the checked edge
theorem called at `ρ = 1` and the swapped-order hypothesis normalized by
`Equiv.swap_inv` and `mul_one`.  It then uses `(4.1)` and `(4.12)` to identify
the compact Euclidean edge distribution with the corrected OS-II Wightman
analytic continuation on the adjacent permuted tube; `(4.12)` here means the
repaired `bvt_F`/`OSLinearGrowthCondition` object, not the false OS-I Lemma
8.8 route.  Equation `(4.14)` supplies Lorentz covariance, after which the
Bargmann-Hall-Wightman theorem continues the adjacent branch across the
connected Figure-2-4/Jost domain `DΩ.Ω`.  The field
`adjacent_lift_pairing_eq_permutedSchwinger` is the continuation of that
compact boundary identity to `x ↦ hChart.adjLift x 0`; it must not be proved
from raw pointwise adjacent-Wick equality, local source equality, PET
independence, EOW, or final `bvt_W` locality.

Paper-transcript tightening for this gate: `(4.1)` is only the ordered-sector
translation-reduced Schwinger distribution identity, `(4.12)` is the
Fourier-Laplace Wightman construction now represented by the repaired
`bvt_F`/`OSLinearGrowthCondition` route, and `(4.14)` is the infinitesimal
Lorentz covariance equation feeding complex-Lorentz invariance before the BHW
continuation.  Therefore the adjacent producer may move to Lean only after
the proof either inlines, or introduces private carriers for, the three real
subclaims named in the blueprint:
`BHW.os45Figure24_adjacentInitialBoundary_of_OSI45_4_1_4_12`,
`BHW.os45Figure24_adjacentLorentzInvariant_of_OSI45_4_14`, and
`BHW.os45Figure24_adjacentBHWContinuation_to_JostDomain`.  The intermediate
`OS45AdjacentPermutedTubeBoundaryFunctional` and
`OS45AdjacentPermutedTubeLorentzInvariantBranch` data, if introduced, must be
proof-local carriers with boundary support, the exact sector identity
`Ωτ = BHW.permutedExtendedTubeSector d n τ`, the corrected Fourier-Laplace
branch identity
`branchτ z = BHW.extendF (bvt_F OS lgc n) (fun k => z (τ k))` on that sector,
and Lorentz/BHW continuation fields.  They may not be `True` predicates,
arbitrary branch choices, or wrappers around
`OS45Figure24AdjacentBranchData`.  The blueprint now includes the
implementation transcript for filling these fields: `Ωτ` is
`BHW.permutedExtendedTubeSector d n τ`, holomorphy comes from
`BHW.extendF_holomorphicOn` composed with the finite coordinate permutation,
the compact boundary pairing is the `bvt_euclidean_restriction`/`OS.E3`
calculation on the selected zero-diagonal test, and Lorentz invariance is
`BHW.extendF_complex_lorentz_invariant` after commuting Lorentz action with
the permutation.  The final continuation packet must additionally produce
`adjacent_realBoundary_eq_ordinary`; otherwise generic Jost/Ruelle uniqueness
would be fed a real-boundary equality that was never proved.

The raw pointwise theorem
`BHW.os45SPrime_rawAdjacentWick_extendF_eq_identityWick_of_BHWJost`, the raw
compact theorem
`BHW.os45SPrime_rawAdjacentWick_extendF_pairing_eq_permutedSchwinger`, and
the comparison
`BHW.os45SPrime_rawAdjacentWick_extendF_pairing_eq_bvt_F` are downstream
consequences after the local source equality has been proved.  They must not
be inputs to the adjacent trace theorem or to the seed proof.  The adjacent
trace theorem also must not be
replaced by the global pointwise theorem `bvt_F_perm`, by final `bvt_W`
locality, by `AdjacentOSEOWDifferenceEnvelope`, or by the global PET
branch-independence consumer.  Until the canonical-lift compact theorem has a
complete OS-I
§4.5/Bargmann-Hall-Wightman/Jost proof transcript, until the source-pullback
rewrite has a complete mechanical transcript from the canonical theorem, and
until the downstream raw comparison is derived only after the local source
equality exists, the adjacent `S'_n` package is not Lean-ready.

Readiness gate for production Lean: the theorem-2 blueprint must remain the
source of truth for Lean-shaped pseudocode.  The scalar-source theorem is not
implementation-ready until its proof is expanded through the Hall-Wightman
Lemma-2 fiber alternative, the singular null-contraction limit, Lemma-3
relative-openness, and Lemmas-4--7 local scalar-product holomorphicity.  The
branch-law rank split in those sublemmas must be the scalar-product rank split
`min d n <= sourceGramMatrixRank` versus `sourceGramMatrixRank < min d n`,
not `SourceComplexGramRegularAt`; the local holomorphic-chart split is the
different maximum-rank threshold `min (d+1) n`.  After the latest doc pass
those are named as the specific sublemmas above, including the power-series
and removable-singularity packet; the
remaining review question before Lean on the scalar-representative theorem is
whether each named Hall-Wightman
sublemma has a fully audited source proof or approved source-import boundary,
not whether theorem-2 may bypass them.  The
adjacent `S'_n` package is not implementation-ready unless the proof keeps the
oriented source-chart provenance needed by the path theorem: the connected
oriented corridor `Wscal`, the real-patch seed neighborhood `Wseed`, the
oriented real patch, the Wick/quarter-turn membership proof, the double
oriented-domain membership, and the Figure-2-4 oriented realization path must
all survive as explicit fields until
`BHW.os45AdjacentSPrimeOrientedSeedFigure24Path_of_compactWickPairingEq` is
proved.  Discarding this provenance and recreating it later would be a
documentation gap, not a Lean convenience.

Compact Figure-2-4 correction for this proof-doc pass: the real patch in
`BHW.OS45CompactFigure24WickPairingEq` is the `π`-permuted canonical source
patch, not the whole half-time common-edge image.  The half-time common edge is
a boundary/Jost chart coordinate and is retained only through the separate
`realPatch_commonEdge_contact` field.  The earlier draft incorrectly supplied
that field from an equal-time `xseed_time0`; this is false, because the checked
selector chooses the ordered perturbation
`xseed = adjacentTimePerturb x0 ε`.  The corrected canonical patch must carry
a second point
`xcontact = os45CommonEdgeRealPoint 1 xseed` with both `xseed ∈ V` and
`xcontact ∈ V`.  Its proof first chooses `ε` so both the perturbation and its
common-edge image stay in `Ufig ∩ Upath` and in the two ordered sectors, then
chooses a connected precompact source patch containing both points by a
segment-thickening argument.  The compact pairing proof therefore pulls tests
back by the pure point-permutation homeomorphism
`BHW.os45SourcePermutationHomeomorph`, proves sector membership from
`V_ET`/`V_swapET`, and reduces the real-patch integral to the canonical source
integral
`∫ extendF (realEmbed u) ψ = ∫ extendF (realEmbed (u ∘ τ)) ψ`.
The load-bearing producer for that reduction is the direct branch-difference
theorem `BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45`;
it is OS-I §4.5 common-boundary/EOW content, not a mechanical rewrite.
Any proof that instead requires continuity of
`extendF` on `realEmbed (os45CommonEdgeRealPoint ... u)` is off route unless a
new genuine boundary-value theorem has first identified that expression with
the appropriate OS45 pulled branch.

The theorem-2 blueprint now retires the earlier individual real-branch
comparison surfaces.  `bvt_euclidean_restriction` rewrites Schwinger
functionals as Wick-rotated `bvt_F` pairings; it does not identify either
real source branch
`∫ extendF (realEmbed x) φ` or
`∫ extendF (realEmbed (x ∘ τ)) φ` separately with `OS.S`.  The missing
OS-I §4.5 content is instead the direct continuation of the **difference**:
compact Wick branch-difference vanishing for every compact test supported in
the chart is transported by
`BHW.os45_adjacent_commonBoundaryEnvelope`,
`BHW.os45CommonBoundary_wickTrace_zero_of_compactPairing_zero`, and
`BHW.os45CommonBoundary_identity_of_wickTrace_zero` to compact real
PET-overlap branch equality.  Until that branch-difference transcript is
complete, the canonical `= OS.S n ψZ` theorem is not enough to start Lean on
the corrected source-patch compact packet.

Adjacent `S'_n` readiness ledger:

| Surface or packet | Current status | Required input before Lean |
| --- | --- | --- |
| `BHW.swFigure24_adjacentPathStableNeighborhood_exists`, `BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability`, `BHW.os45_adjacent_identity_horizontalEdge_sourcePatch` | Checked local Lean geometry in `OSToWightmanLocalityOS45Figure24.lean`. | May supply `hV_adjLift_ET`, closure ordered-sector fields, and `hV_figPath_closure`; it supplies no scalar equality. |
| `BHW.OS45Figure24RotatedPathFormulaField`, `BHW.swFigure24_adjacentPathStableNeighborhood_rotated_exists`, `BHW.OS45Figure24OrientedPathField_of_checked_figure24`, `BHW.swFigure24_adjacentHorizontalEnvironmentWithRotatedPathStability`, `BHW.os45_adjacent_identity_horizontalEdge_sourcePatch_with_orientedPath`, `BHW.os45Figure24AdjacentLift`, `BHW.continuous_os45Figure24AdjacentLift`, `BHW.os45Figure24AdjacentLift_sourceGram`, `BHW.swFigure24_adjacentPathStableCanonicalLift_exists`, `BHW.OS45Figure24CanonicalSourcePatchData`, `BHW.OS45Figure24OrientedCanonicalSourcePatchData`, `BHW.exists_os45_adjacent_identity_canonicalSourcePatch_with_orientedPath`, `BHW.os45_adjacent_identity_canonicalSourcePatch_with_orientedPath`, and `BHW.os45_adjacent_identity_canonicalSourcePatch` | Checked in `OSToWightmanLocalityOS45Figure24.lean`.  The final canonical packet is now packaged as an existential theorem in `Prop` plus `noncomputable def` selectors, which is the correct Lean shape for data chosen from upstream existence theorems. | The checked slice exposes the definitional rotated `Δ t = figure24RotateAdjacentConfig hd (permAct τ (os45Figure24IdentityPath x t))`, the deterministic lift `os45Figure24AdjacentLift`, source-Gram identity for that lift, full oriented invariant equality using `sourceOrientedMinkowskiInvariant_complexLorentzAction` and `sourceOrientedMinkowskiInvariant_permAct`, the corrected `xseed`/`xcontact = os45CommonEdgeRealPoint 1 xseed` contact fields, the whole segment containment needed for the compact shrink, and the closure-level oriented path field needed by the strict adjacent `S'_n` source-germ suppliers. |
| `BHW.sourceOrientedGramVariety_local_connectedRelOpen_basis`, `BHW.sourceOrientedGramVariety_connectedComponentIn_relOpen`, `BHW.sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath` | Source-geometry transcript partially checked: max-rank chart topology/germ-pullback/local-identity is checked in `SourceOrientedLocalChart.lean`; connected-component and path-tube assembly are checked in `SourceOrientedConnected.lean`; the stratum dispatcher is checked in `SourceOrientedLocalBasis.lean`; the rank-deficient local-image output interface is checked in `SourceOrientedRankDeficientLocalImage.lean`. | Needed because oriented `Wscal` is now a connected component of the oriented adjacent double domain.  The component theorem is now Lean, conditional only on a local connected basis: write `D = D0 ∩ sourceOrientedGramVariety`, index local connected patches by `{G // G ∈ connectedComponentIn D G0}`, get each patch from the local basis inside `D0`, put it into the component by `IsPreconnected.subset_connectedComponentIn`, identify components by `connectedComponentIn_eq`, and take an indexed union using `IsRelOpenInSourceOrientedGramVariety.iUnion`.  The local connected basis is decomposed into two producer inputs.  Max-rank patches use the checked `SourceOrientedMaxRankChartData.exists_connected_chartBall`, `inv_image_openBall_relOpen`, `connectedPatch_inside_open`, `shrink_to_relOpen`, finite-coordinate transport `finiteDimensionalCoordinateEquiv`, `to_finrankCoordinateChart`, and `local_identity_near_point_finiteDimensional`.  Germ pullback and relative-openness transfer through such a chart are checked as `LocalBiholomorphOnSourceOrientedVariety.germ_to_chart`, `SourceOrientedVarietyGermHolomorphicOn.to_maxRank_chart`, and `LocalBiholomorphOnSourceOrientedVariety.image_relOpenIn_chart`.  The chart-local identity theorem is checked as `SourceOrientedMaxRankChartData.local_identity_near_point` for finite coordinate models, using the finite-dimensional `SCV.identity_theorem_connected_open_zero`; the earlier arbitrary-normed-model identity statement is intentionally not used.  The chart packet explicitly carries `chart_continuousOn`, since relative openness of inverse-image patches otherwise would be unjustified.  Rank-deficient patches now have the checked abstract packet `SourceOrientedRankDeficientVarietyLocalImageData`, subtype adapter `SourceOrientedRankDeficientVarietyLocalImageData.ofSubtype`, and extraction theorem `to_connectedRelOpenPatch`; the concrete no-tube algebraic local-image producer still must be built from `SourceOrientedRankDeficientAlgebraicNormalFormData`, the signature-metric head gauge `SourceRankDeficientHeadGaugeData`, Schur residual extraction, `sourceShiftedTailSmallRealization`, and the target-shaped tail-window choice.  The algebraic parameter-window output must carry its normal image neighborhood `Ωnf` explicitly; the connected parameter set must include raw head/mixed/tail coordinate bounds and the shifted-tail invariant inequalities below the chosen `tailEta`; and `schurParam_mem` must record that extracted head/mixed/tail parameters land back in that same window.  The extended-tube compact residual chart is explicitly not an input to this basis theorem.  Next Lean targets are the finite-coordinate max-rank chart producer and the concrete rank-deficient Schur/residual local-image producer; not connected-component support and not the Figure-2-4 seed wrapper. |
| `BHW.os45AdjacentSPrimeOrientedScalarizationChart_of_figure24` | Constructor transcript pinned; production Lean not started. | Must combine the checked source patch with `sourceOrientedExtendedTubeDomain_relOpen_connected`, oriented double-domain relative openness, Wick real-section topology, and oriented germ pullback APIs.  Its `Wscal` must also store `Wscal_component : ∃ Gbase ∈ Wscal, Wscal = connectedComponentIn (sourceOrientedDoublePermutationDomain d n τ) Gbase`; closure-level quarter-turn membership is not justified from relative openness alone. |
| `BHW.os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45` | Route-cycle corrected; direct producer transcript pinned, first carrier/algebra layer now checked below the public surface. | Must now construct the checked `BHW.OS45SourcePatchBHWJostPairData` carriers directly from OS I §4.5/BHW-Jost data, preferably on the exact canonical source patch `BHW.os45Figure24SourcePatch`; if the producer constructs a larger source patch, it must also prove canonical source-patch containment.  The checked exact-source-patch and canonical consumers then derive compact Wick equality from the carrier itself: Wick compact zero comes from the Euclidean-edge theorem, `P.difference` propagation is checked, real-boundary integration is checked, and family/source-anchor packaging is checked.  A separate `OS45SourcePatchBHWJostDifferenceData` wrapper is not a first target unless it carries additional source provenance beyond the checked pair-data fields.  It cannot use `BHW.os45_adjacent_commonBoundaryEnvelope`, the oriented branch-germ suppliers, the oriented adjacent `S'_n` seed/path package, individual real-branch `= OS.S` statements, PET independence, final locality, or the later OS-specific `JostRuelleCompactBoundaryData` package that consumes this compact theorem. |
| `BHW.os45CommonBoundary_wickTrace_zero_of_compactPairing_zero` and `BHW.os45CommonBoundary_identity_of_wickTrace_zero` | Proof transcript pinned; production Lean not started. | The first applies the checked `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` to the Wick trace function `g`, with `ContinuousOn g V0` from `hHc_holo.continuousOn.comp`, and uses `BHW.integral_commonBoundary_wickTrace_eq_zero_of_wickDiff_zero` to rewrite the compact pairings. The second defines `Lρ := os45WickRotateCLE.trans (os45CommonChartCLE 1)`, `U' := Lρ ⁻¹' Uc`, `H' z := Hc (Lρ z)`, proves `IsConnected U'` by Mathlib `Homeomorph.isConnected_preimage` (`.2 hUc_conn`), and applies checked `BHW.identity_theorem_totally_real_product` on the standard real slice after `BHW.os45CommonChartCLE_wickRotateRealConfig_eq`. No scalar representative, PET, EOW shortcut, or locality input enters these two helpers. |
| `BHW.OS45SourcePatchBHWJostHullData`, `BHW.os45_sourcePatch_bhwJostHullData_on_figure24SourcePatch`, `BHW.OS45SourcePatchBHWJostPairData`, `BHW.continuous_wickRotateRealConfig`, `BHW.differentiable_permAct`, `BHW.isOpen_permAct_preimage_extendedTube`, `BHW.differentiableOn_extendF_bvt_F_extendedTube`, `BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube`, `BHW.integrable_bvt_F_wickRotate_mul_schwartz_of_orderedSector`, `BHW.integrable_wickEdge_bvt_F_mul_schwartz_of_orderedSector`, `BHW.integrable_extendF_realSource_mul_schwartz_of_ET`, `BHW.integrable_wickEdge_bvt_F_mul_schwartz_on_figure24SourcePatch`, `BHW.integrable_extendF_realSource_mul_schwartz_on_figure24SourcePatch`, `BHW.integrable_extendF_swapRealSource_mul_schwartz_on_figure24SourcePatch`, `BHW.integral_wickBranchDifference_mul_eq_zero_of_pairing_eq`, `BHW.os45_wickBranchDifference_zero_of_euclideanEdge_pairing_eq_on_timeSector`, `BHW.os45_wickBranchDifference_zero_on_figure24SourcePatch`, `BHW.OS45SourcePatchBHWJostPairData.restrict`, `BHW.OS45SourcePatchBHWJostPairData.restrict_figure24SourcePatch`, `BHW.OS45SourcePatchBHWJostPairData.ofHullDataAndBranches`, `BHW.OS45SourcePatchBHWJostPairData.difference`, `BHW.OS45SourcePatchBHWJostPairData.difference_holo`, `BHW.OS45SourcePatchBHWJostPairData.difference_wick_trace`, `BHW.OS45SourcePatchBHWJostPairData.difference_real_trace`, `BHW.os45_pairData_difference_identity_of_wickDistributionZero`, `BHW.os45_pairData_difference_realTrace_zero_of_wickDistributionZero`, `BHW.realSourceBranchDifference_zero_of_pairData_difference_zero`, `BHW.integral_realSourceBranchDifference_eq_zero_to_pairing_eq`, `BHW.os45Figure24_sourcePatch_pairing_eq_of_realSourceBranchDifference_zero`, `BHW.os45CompactFigure24WickPairingEq_of_realSourceBranchDifference_zero`, `BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero`, `BHW.os45CompactFigure24WickPairingEq_of_pairData_difference_zero_canonical`, `BHW.os45CompactFigure24WickPairingEq_of_pairData_canonical`, `BHW.os45CompactFigure24WickPairingEq_of_pairData_on_figure24SourcePatch`, `BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero`, `BHW.os45CompactFigure24WickPairingEq_family_of_pairData_difference_zero_canonical`, `BHW.os45CompactFigure24WickPairingEq_family_of_pairData_canonical`, `BHW.os45CompactFigure24WickPairingEq_family_of_pairData_on_figure24SourcePatch`, `BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero`, `BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_difference_zero_canonical`, `BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_canonical`, `BHW.sourceDistributionalAdjacentTubeAnchor_of_pairData_on_figure24SourcePatch`, `BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_difference_zero`, `BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_difference_zero_canonical`, `BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_canonical`, `BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_pairData_on_figure24SourcePatch`, `BHW.bvt_F_distributionalJostAnchor_of_pairData_difference_zero`, `BHW.bvt_F_distributionalJostAnchor_of_pairData_difference_zero_canonical`, `BHW.bvt_F_distributionalJostAnchor_of_pairData_canonical`, and `BHW.bvt_F_distributionalJostAnchor_of_pairData_on_figure24SourcePatch` | Checked in `OSToWightmanLocalityOS45BHWJost.lean`. | This layer records the two ordinary/adjacent BHW-Jost branches on one connected source hull, their Wick traces, and their real source traces.  The checked restriction constructors shrink a carrier to any smaller open source patch, especially the canonical Figure-2-4 source patch.  The checked Wick integrability support proves the identity Wick trace integrable on an ordered source patch and every permuted Wick trace integrable there by `bvt_F_perm`; the checked real-source integrability support proves the corresponding `extendF` traces integrable from extended-tube membership, continuity of real embedding/permutation, and `BHW.extendF_holomorphicOn`; the checked canonical specializations discharge these hypotheses on `os45Figure24SourcePatch`.  The checked algebra subtracts the two branches, proves holomorphy of the difference, rewrites equality of the two compact Wick pairings as zero of the Wick branch-difference pairing under explicit integrability hypotheses, converts the checked OS45 Euclidean-edge compact pairing theorem into canonical Wick branch-difference zero, upgrades compact-test Wick-trace distributional zero to pointwise zero of `P.difference` on the connected hull by the existing Wick-real-section identity theorem, rewrites this as real-source `P.difference` distributional zero, converts the explicit real source-branch zero into equality of compact real source pairings, packages that equality into `BHW.OS45CompactFigure24WickPairingEq`, and folds a full adjacent family into both the selected-anchor and direct source-anchor surfaces.  The exact-source-patch variants leave only the pair carrier on `BHW.os45Figure24SourcePatch` as input; the broader canonical variants leave the pair carrier plus canonical source-patch containment.  It does not construct the carrier from OS I §4.5; that carrier producer is the remaining direct BHW/Jost source obligation. |
| `BHW.os45SourcePermutationHomeomorph` and `BHW.os45Figure24CompactRealPatch_*` geometry accessors | Checked in `OSToWightmanLocalityOS45Figure24.lean`. | Defines the homeomorphism by `u ↦ fun k μ => u (π.symm k) μ` and the compact real patch as its image of `BHW.os45Figure24SourcePatch`.  Openness is `Homeomorph.isOpenMap`; nonemptiness and contact come from the checked canonical packet; Jost membership is `BHW.jostSet_permutation_invariant π.symm`; left/right sector fields unfold `BHW.permutedExtendedTubeSector` and use the checked source-patch ordinary/swapped `ExtendedTube` accessors.  No `extendF`, scalar representative, compact branch equality, PET, EOW, or locality input enters this layer. |
| `BHW.os45CompactRealPatch_pullbackSchwartz` | Checked in `OSToWightmanLocalityOS45Figure24.lean`. | Sets `ψ := BHW.permuteSchwartz π.symm φ`, uses `BHW.permuteSchwartz_hasCompactSupport`, `BHW.tsupport_permuteSchwartz`, injectivity of `BHW.os45SourcePermutationHomeomorph`, and `(BHW.integral_perm_eq_self π.symm h).symm` twice.  The only branch rewrites are finite-coordinate equalities; no `bvt_F`, OS-I branch-difference, scalar representative, PET, EOW, or locality input enters. |
| `BHW.OS45CompactFigure24WickPairingEq`, `BHW.os45CompactFigure24WickPairingEq_of_sourcePatchPairing`, `BHW.OS45CompactFigure24WickPairingEq.leftSourcePatch`, `BHW.sourceDistributionalAdjacentTubeAnchor_of_compactWickPairingEq`, `BHW.bvt_F_selectedAdjacentDistributionalJostAnchorData_of_compactWickPairingEq`, and `BHW.bvt_F_distributionalJostAnchor_of_compactWickPairingEq` | Compact packet, ordinary source-anchor conversion, and selected-witness compatibility bridge checked in `OSToWightmanLocalityOS45Compact.lean`; the hard compact branch equality remains the input.  The oriented real-seed/anchor layer is still downstream and not implemented. | The compact packet stores the `π`-permuted source real patches, left/right `ExtendedTube` sector fields, a separate common-edge contact, and compact distributional branch equality. The constructor from canonical source-patch pairing is mechanical: use the checked canonical packet fields, `BHW.os45CompactRealPatch_pullbackSchwartz`, and the source-patch equality over `extendF (realEmbed u)` and `extendF (realEmbed (u ∘ τ))`; it does not prove that equality.  A full family of compact packets over all adjacent swaps now builds the existing `BHW.SourceDistributionalAdjacentTubeAnchor` by taking Gram environments to be the images of the unlabelled left source patches under `sourceRealMinkowskiGram`; uniqueness is supplied by `BHW.sourceDistributionalUniquenessSetOnVariety_of_open_jost_patch`, and `gram_right_eq_perm_left` is the finite identity `sourceRealMinkowskiGram_perm`.  The selected-witness bridge takes the identity-labelled compact patch as the base patch and reuses the same uniqueness and compact equality fields, avoiding an import cycle in `OSToWightmanSelectedWitness.lean`.  The future oriented adjacent `S'_n` seed still must shrink to determinant-regular real subpatches and prove oriented source equality; it must not treat this ordinary source anchor as an oriented uniqueness theorem. |
| `BHW.os45Figure24SourcePatch`, `BHW.os45Figure24SourcePatch_sourceEnvironment`, and source-patch accessors | Checked in `OSToWightmanLocalityOS45Figure24.lean`. | Defines `os45Figure24SourcePatch` as the proof-irrelevant canonical `V`, proves equality to `(os45_adjacent_identity_canonicalSourcePatch hd i hi).V`, and exports open/nonempty/Jost/ET/swapped-ET/ordered/swapped-ordered/deterministic-lift fields plus `os45Figure24SourcePatch_wick_mem_extendedTube`, `os45Figure24SourcePatch_permAct_realEmbed_mem_extendedTube`, `os45Figure24SourcePatch_closure_orientedPath`, and `os45Figure24SourcePatch_sourceEnvironment`.  The checked packet now carries an explicit `τ_eq` field; a default value for the structure field is not enough after `Classical.choose`.  These accessors are projections from the checked canonical/oriented packet, not new scalar equality or locality inputs.  There is intentionally no `os45Figure24SourcePatch_permAct_wick_mem_extendedTube` accessor, since the swapped ordered-sector field does not imply that statement. |
| `BHW.Figure24LocalChartInput` and the source-patch compact partition | Shape corrected for the oriented route; production Lean not started. | Every local chart input used by `os45CanonicalSourcePatch_extendF_eq` must carry both `V_sourcePatch : V ⊆ os45Figure24SourcePatch d n i hi` and `V_orientedPath_closure : ∀ x ∈ closure V, OS45Figure24OrientedPathField d n i hi x`.  For the direct compact branch-difference theorem, `V_sourcePatch` supplies the checked source-patch geometry and the local BHW/Jost carrier input on `hChart.V0`; it does not authorize a call to the oriented branch-germ suppliers.  The closure-level oriented path field is retained for the downstream oriented adjacent `S'_n` seed/path package and branch-germ suppliers after the compact packet is built.  The compact partition must use `BHW.os45_adjacent_identity_canonicalSourcePatch_with_orientedPath`, set `P := Poriented.toCanonical`, and fill the input fields by `P.V = os45Figure24SourcePatch` and `Poriented.orientedPath_closure`; otherwise the partition silently drops the determinant path or the pulled-domain source environment.  When a partition subchart `hChart.V0 ⊆ V` is used, transfer the oriented path field by `BHW.closure_sourceChart_sub_closure_input`.  The older pure-Gram `hV_figPath_closure` is insufficient for the active oriented source-germ suppliers. |
| `BHW.sourceOrientedAnchor_compactBranchEq_pointwise_on_realPatch` | Proof-doc pseudo-code tightened. | Before using the scalar representative, convert `hAnchor.compact_branch_eq` to pointwise equality on the real patch by `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`, with continuity supplied by `extendF_continuousOn_realPatch_left/right`, the anchor's left/right sector fields, and the complex-Lorentz invariance input needed by `BHW.extendF_holomorphicOn`. |
| `BHW.os45Figure24_checkedRealPatch_chartContact`, `BHW.os45Figure24_checkedRealPatch_shrink_into_orientedRelOpen`, `BHW.os45Figure24_realPatch_orientedRegularChartSubpatch` | Chart-compatible real-patch transcript pinned; production Lean not started. | First prove the raw checked real patch contacts `hChart.Wscal`; then shrink the checked patch through the relatively open chart preimage while preserving the checked OS45 real environment; only after that impose determinant-regular oriented environment. This supplies the explicit `hE_chart` membership needed by the seed theorem. |
| `BHW.os45_oriented_seedNeighborhood_from_realPatch` | Pseudo-code corrected. | It no longer infers chart membership from raw anchor membership. It consumes `hE_chart` and chooses `Wseed := hChart.Wscal`, giving relative openness, connectedness, nonemptiness, double-domain membership, and real-patch image membership directly from the chart fields. |
| `BHW.os45AdjacentSPrimeOrientedRealSeed_of_compactWickPairingEq` | Assembly transcript pinned; production Lean not started because its upstream producers remain first. | Use the chart-compatible real-patch shrink, prove equality on the shrunken real patch by `sourceOrientedScalarRepresentative_adjacent_seed_eq_on_patch` in the orientation `Φ (sourcePermuteOrientedGram τ (sourceRealOrientedMinkowskiInvariant y)) = Φ (sourceRealOrientedMinkowskiInvariant y)`, use `sourceOrientedDistributionalUniquenessPatch_of_HWRealEnvironment` to get `seed_eq` on `Wseed`, and retain `realPatch`, `Wseed`, `Wseed_subset_Wscal`, `Wseed_double`, and `wick_mem`.  Its remaining blockers are upstream producer theorems: chart-compatible real-patch shrink, oriented real uniqueness, scalar representative branch equality, and the compact Figure-2-4 pairing packet. |
| `BHW.os45AdjacentSPrimeOrientedSourceEq_of_realSeed` and `BHW.os45AdjacentSPrimeOrientedSourceEq_of_compactWickPairingEq` | Final orchestration only after the real seed. | Call `BHW.os45AdjacentOrientedScalarEq_on_quarterTurnCorridor` with the real seed and chart; do not reprove the identity principle or derive equality directly from compact Wick pairing without the seed object. |
| `BHW.os45AdjacentSPrimeOrientedScalarSeed_of_compactWickPairingEq` | Assembly transcript pinned; production Lean not started because the real-seed producer is blocked. | Let `hRealSeed := os45AdjacentSPrimeOrientedRealSeed_of_compactWickPairingEq`, then call `BHW.os45AdjacentSPrimeOrientedScalarSeed_of_realSeed`.  The assembly packages the real seed and chart fields into the path-facing seed structure, including the actual permutation equality `τ_eq`, `Wseed_subset`, `Wscal_double`, and the chart's `Wscal_component`, so later closure proofs know that `Wscal` is the selected connected component of the oriented adjacent double domain. |
| `BHW.os45AdjacentSPrimeOrientedSeedFigure24Path` | Assembly proof pinned. | Stores the provenance seed, the supplied closure path field, and `quarterTurn_mem_closure`, then calls `BHW.os45AdjacentOrientedScalarEq_on_quarterTurnCorridor`; the only subtle step is rewriting through `hSeed.τ_eq` so the seed's stored `τ` is the fixed adjacent swap. |
| `BHW.os45AdjacentSPrimeOrientedQuarterTurnMem_closure_of_figure24Path` | Proof transcript pinned; production Lean not started. | Requires `V.Nonempty`, `IsConnected V`, `V ⊆ hSeed.V`, `OS45Figure24OrientedPathField` on `closure V`, continuity of the quarter-turn oriented scalar map, oriented double-domain membership from the endpoint `Γ, Δ` path, and the stored `Wscal_component`.  The exact topology APIs are `IsConnected.closure`, `IsConnected.image`, `IsPreconnected.subset_connectedComponentIn`, and `connectedComponentIn_eq`; do not use `closure V ⊆ hSeed.V` or a closedness/relative-openness shortcut. |
| `BHW.os45AdjacentSPrimeOrientedSeedFigure24Path_of_compactWickPairingEq` | Assembly transcript pinned; production Lean not started because its producers are blocked. | Build `hChart`, `hSeed0`, restrict the seed to the local source patch `V` using only `V ⊆ hSeed.V`, transport the supplied oriented path field along the restricted seed, pass in `quarterTurn_mem_closure`, and call `BHW.os45AdjacentSPrimeOrientedSeedFigure24Path`.  It must **not** assume `closure V ⊆ hSeed.V`.  The checked `hV_figPath_closure` must be strengthened to `OS45Figure24OrientedPathField` on `closure V`, and `quarterTurn_mem_closure` must be proved by `BHW.os45AdjacentSPrimeOrientedQuarterTurnMem_closure_of_figure24Path` using connected-component propagation over `closure V`. |
| Generic post-seed oriented corridor propagation | Assembly proof transcript pinned; production Lean not started until the oriented identity principle exists. | `BHW.os45AdjacentOrientedScalarEq_on_quarterTurnCorridor` mirrors the checked `BHW.os45AdjacentScalarEq_on_quarterTurnCorridor`: define `Φ G := hRep.Phi (sourcePermuteOrientedGram d n τ G)` and `Ψ := hRep.Phi`, obtain `hΨ_holo` by restricting `hRep.Phi_holomorphic` to `Wscal`, obtain `hΦ_holo` from checked `SourceOrientedVarietyGermHolomorphicOn.precomp_sourcePermuteOrientedGram`, subtract, prove zero on `Wseed` from `hSeed`, and apply `sourceOrientedGramVariety_identity_principle` on the connected relatively open `Wscal`.  The basic oriented germ API and double-domain topology are checked in `SourceOriented.lean`; the remaining generic input is the oriented source-variety identity principle, while the OS-specific inputs remain the oriented scalarization chart, compact Figure-2-4 seed, and real-seed provenance package. |

Implementation detail for the real-seed proof: the continuity and
compact-to-pointwise conversion for `extendF` require the local checked
theorems `bvt_F_holomorphic` and
`bvt_F_complexLorentzInvariant_forwardTube` in the Wick-rotation namespace,
transported across `BHW_forwardTube_eq` to the `BHW.ForwardTube` API.  The
restricted theorem `bvt_F_restrictedLorentzInvariant_forwardTube` is useful
for real-Lorentz covariance statements elsewhere, but it is not enough for
the `BHW.extendF_holomorphicOn` continuity input expected by
`sourceOrientedScalarRepresentative_adjacent_seed_eq_on_patch`.
Its equality direction is load-bearing: the seed uniqueness call compares
`fun G => hRep.Phi (sourcePermuteOrientedGram d n τ G)` against
`hRep.Phi`, so the real-patch hypothesis must be the same
`permuted = identity` orientation.  Reversing that equality is not a harmless
presentation choice, because it changes which holomorphic germ is the left
side of the propagated `Set.EqOn`.

The checked rows are geometry/topology inputs only.  The oriented
scalar-equality rows remain blocked until the oriented scalar representative,
oriented real-patch uniqueness, and OS-I compact adjacent branch producer are
proved.

Active-route guard, 2026-05-02: any theorem-2 proof text below that still
mentions the ordinary pure-Gram hypothesis
`hRep : SourceScalarRepresentativeData (d := d) n (bvt_F OS lgc n)` is an
archived conditional consumer note, not a strict-route Lean target.  The
strict OS I §4.5 route after the canonical compact theorem is the oriented
chain:

```text
os45Figure24_sourcePatch_pairing_eq_swappedSourcePatch_of_OSI45
  -> OS45CompactFigure24WickPairingEq
  -> sourceOrientedAdjacentTubeAnchor_of_compactWickPairingEq
  -> os45AdjacentSPrimeOrientedRealSeed_of_compactWickPairingEq
  -> os45AdjacentSPrimeOrientedSourceEq_of_realSeed
  -> os45AdjacentSPrimeOrientedSeedFigure24Path_of_compactWickPairingEq
  -> os45OneBranchOrientedSourceEq_sourceInput_adjacent
  -> os45BranchHorizontalOrientedSourceGermAt_of_figure24_adjacent
  -> os45_adjacent_commonBoundaryEnvelope
```

Do not start Lean from the ordinary
`os45AdjacentWickTrace_sourceScalarRepresentative...` or
`os45SPrime_sourcePullback...` names unless the separate full-component
Hall-Wightman fork has first produced
`BHW.sourceScalarRepresentativeData_bvt_F`.  On the active route those names
are replaced by the oriented real-seed, oriented source-equality, and
oriented branch-germ producers listed above.

Route correction for the next Lean pass: do not spend effort rebuilding the
generic corridor identity-principle proof on the pure-Gram API.  On the
active route, implement the oriented analog only after
`sourceOrientedGramVariety_identity_principle` is ready.  Once the OS-specific
compact pairing seed supplies
`Set.EqOn (fun G => hRep.Phi (BHW.sourcePermuteOrientedGram d n τ G))
hRep.Phi Wseed`, and the Figure-2-4 provenance/path theorem supplies a
connected relatively open `Wscal` with `Wseed ⊆ Wscal` inside
`sourceOrientedDoublePermutationDomain d n τ`, the intended consumer is
`BHW.os45AdjacentOrientedScalarEq_on_quarterTurnCorridor`.  The still-missing
mathematics is upstream: the oriented scalarization chart, the compact OS-I
§4.5 adjacent pairing theorem, and the provenance-preserving oriented real
seed package.

The current proof-document pass now separates upstream and downstream source
content:

1. `hUfig_source` is explicitly only domain geometry.  It supplies Jost
   membership, identity/adjacent extended-tube membership, and the two OS45
   pulled-domain memberships; it does not compare branch values.
2. `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_id` and
   `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_adjacent` are upstream
   one-branch OS I §4.5/BHW source suppliers.  They must also consume the
   closure-level ordered-sector fields from the selected `V`: the identity
   supplier uses `hV_ordered_closure`, and the adjacent supplier uses both
   `hV_ordered_closure`, `hV_swap_ordered_closure`, and the oriented
   Figure-2-4 path closure after relabelling.  These
   ordered fields are not optional, because they are what make
   `BHW.os45CommonEdge_mem_acrBranchDomain_of_ordered` available at the
   horizontal base point.  The adjacent scalar packet is produced in the
   original identity coordinates at
   `y0 = BHW.os45CommonEdgeRealPoint 1 x`; the one-branch source-patch assembly
   is then applied on the relabelled ordered branch `x ∘ τ` after rewriting the
   packet basepoint by `BHW.os45CommonEdgeRealPoint_adjacent_swap_eq`, and the
   packaged source-germ predicate is rewritten back to `y0` by the same checked
   equality.  This is only basepoint transport for one branch.  It must not use
   an
   `AdjacentOSEOWDifferenceEnvelope`, real-edge adjacent equality, final
   `bvt_W` locality, or global PET branch independence.
3. Both suppliers factor through the exact one-branch conversion
   `BHW.os45BranchHorizontalSourceGermAt_of_orientedSourceEq`, after first
   constructing the branch's oriented scalar packet.  Its
   genuine content is the BHW source/edge statement that, on one selected
   Figure-2-4 source patch and for one fixed branch label `β`, the OS-II ACR
   representative `bvt_F (permAct β.symm (Q.symm z))` and the pulled BHW
   representative `extendF (bvt_F) (permAct β.symm (Q.symm z))` are two
   continuations of the same local germ.  This former proof-doc target has now
   been expanded as a one-branch BHW theorem, not as adjacent equality.  The
   theorem is split in the blueprint into a pure source-neighborhood
   geometry part and the genuine oriented value-agreement theorem
   `BHW.os45OneBranchOrientedACRBHWAgreement_of_sourcePatch`.  The geometry fields
   choose the neighborhood, use ordered-sector membership for the ACR side,
   and ensure the pulled BHW argument lies in the extended tube; they do
   **not** prove the ACR/BHW equality.  Jost and ordinary extended-tube fields
   remain upstream in the scalar-packet suppliers; the generic source-patch
   assembly no longer carries them after `hScalar` is supplied.  The agreement
   theorem is now further split, on the archived pure-Gram side, around the
   explicit scalar packet
   `BHW.OS45OneBranchScalarGramEqPacket`: the public identity and adjacent
   source suppliers produce this packet, while
   `BHW.os45OneBranchACRBHWAgreement_sourceInput` only consumes it and converts
   it into a neighborhood contained in both branch domains plus the required
   `Set.EqOn` equality.  The packaging theorem
   `BHW.os45OneBranchACRBHWAgreement_of_sourcePatch` also consumes the same
   packet together with the source-patch geometry.  The algebraic reduction from
   local Gram equality to ACR/BHW equality is now named
   `BHW.os45OneBranchACRBHWAgreement_of_scalarGramEq`: after a
   `SourceScalarRepresentativeData` packet supplies equality of the two
   scalar-product Gram arguments, the proof is just the checked orientation of
   `SourceScalarRepresentativeData.branch_eq`, `sourceMinkowskiGram_perm`,
   `bvt_F_perm`, and
   `BHW.extendF_eq_on_forwardTube`.  The scalar packet must be produced from
   the explicit local `S'_n` source suppliers
   `BHW.os45OneBranchScalarGramEq_sourceInput_id` and
   `BHW.os45OneBranchScalarGramEq_sourceInput_adjacent`; there is no public
   arbitrary-`β` theorem manufacturing it from source-domain geometry alone.
   These suppliers obtain the ordinary `SourceScalarRepresentativeData`,
   construct a relatively open scalar neighbourhood inside the relevant double
   scalar domain, prove equality of `Phi` and its permuted pullback from the
   identity simplification or the OS-II symmetric `S'_n` seed, and then pull
   the result back through
   `sourceMinkowskiGram (Q.symm z)`.  On the active theorem-2 route this
   paragraph must be read through the oriented replacement names below: replace
   the scalar packet by `BHW.OS45OneBranchOrientedSourceEqPacket`, replace
   `SourceScalarRepresentativeData` by
   `SourceOrientedScalarRepresentativeData`, and replace every Gram/double
   domain by the oriented invariant and oriented double-domain.  The first
   theorem-2 Lean pass must implement the oriented version before touching the
   downstream EOW envelope.  The oriented algebraic reduction is now pinned in
   the blueprint as
   `BHW.os45OneBranchOrientedACRBHWAgreement_of_orientedScalarEq`: for
   `u := Q.symm z` and
   `w := BHW.permAct β.symm u`, it rewrites
   `sourceOrientedMinkowskiInvariant w` by
   `BHW.sourceOrientedMinkowskiInvariant_permAct
   (d := d) (n := n) β.symm u`, applies the
   packet equality on
   `sourceOrientedMinkowskiInvariant u`, rewrites both sides by
   `SourceOrientedScalarRepresentativeData.branch_eq`, reduces the forward
   side with `BHW.extendF_eq_on_forwardTube`, and finishes by
   `bvt_F_perm OS lgc n β.symm u`.  This is the only allowed consumer-side
   conversion from an oriented source packet to one-branch ACR/BHW equality.

   Fork compatibility guard: the theorem surfaces named in this scalar-packet
   order are pure-Gram surfaces.  In particular,
   `BHW.os45BranchHorizontalSourceGermAt_of_oneBranch_sourcePatch`,
   `BHW.os45OneBranchACRBHWAgreement_of_sourcePatch`,
   `BHW.os45OneBranchACRBHWAgreement_sourceInput`,
   `BHW.os45OneBranchACRBHWAgreement_of_scalarGramEq`,
   `BHW.os45OneBranchScalarGramEq_sourceInput_id`,
   `BHW.os45OneBranchScalarGramEq_sourceInput_adjacent`,
   `BHW.os45SPrime_figure24LocalSourceEq_of_BHWJost`, and
   `BHW.os45SPrime_figure24LocalBranchCompatibility_of_BHWJost` may be ported
   only after `BHW.sourceScalarRepresentativeData_bvt_F` is available from the
   full-component pure-Gram Hall-Wightman source gate.  Since the strict OS
   §4.5 source decision is now the proper-complex/oriented repair, these names
   must be replaced before Lean by the oriented packet and consumer names:
   `BHW.os45OneBranchOrientedSourceEq_sourceInput_id`,
   `BHW.os45OneBranchOrientedSourceEq_sourceInput_adjacent`,
   `BHW.os45OneBranchOrientedACRBHWAgreement_sourceInput`,
   `BHW.os45OneBranchOrientedACRBHWAgreement_of_sourcePatch`,
   `BHW.os45BranchHorizontalSourceGermAt_of_orientedSourceEq`,
   `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_id`,
   `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_adjacent`,
   `BHW.os45SPrime_figure24LocalOrientedSourceEq_of_BHWJost`, and
   `BHW.os45SPrime_figure24LocalOrientedBranchCompatibility_of_BHWJost`.
   The two active oriented packet producers now have explicit local
   source-input shapes in the blueprint.  The identity producer
   `BHW.os45OneBranchOrientedSourceEq_sourceInput_id` takes the oriented
   scalar representative plus the base point's membership in the identity
   ACR and pulled-BHW branch domains, chooses `Wscal := hRep.U`, builds `Uy`
   from an ambient-open representative of `hRep.U_relOpen`, proves the double
   domain by `BHW.sourceOrientedDoublePermutationDomain_one_eq`, and proves
   equality by `BHW.sourcePermuteOrientedGram_one`.  The adjacent producer
   `BHW.os45OneBranchOrientedSourceEq_sourceInput_adjacent` consumes an
   `OS45AdjacentSPrimeOrientedSeedFigure24Path` packet, the base point's
   adjacent ACR/pulled-domain memberships, and the quarter-turn oriented
   scalar membership in `hPath.seed.Wscal`, supplied on closure points by
   `hPath.quarterTurn_mem_closure`; it builds `Uy` from the same rel-open
   pullback and uses `hPath.corridor_eq`, `hPath.seed.Wscal_double`,
   `hPath.seed.τ_eq`, and the self-inverse adjacent swap to fill the packet.
   This pins the only place where oriented Figure-2-4 path provenance enters
   the one-branch source packet.
   The adjacent Figure-2-4 branch-germ supplier now carries
   `hV_open`, `hV_nonempty`, `hV_connected`, and
   `V ⊆ BHW.os45Figure24SourcePatch`; these are needed to build the localized
   seed/path packet and must be supplied by the oriented canonical source
   patch.  The supplier transcript explicitly constructs `hRep`, `hCompact`,
   `hQuarterTurn_mem_closure`, `hPath`, `hy_acr`, `hy_bhw`, `hy_scalar`, then
   calls the adjacent packet producer and finally
   `os45BranchHorizontalSourceGermAt_of_orientedSourceEq`.
   The common-boundary envelope still consumes the neutral predicate
   `OS45BranchHorizontalSourceGermAt`; on the active route that predicate must
   be produced by these oriented suppliers, not by the archived pure-Gram
   source-patch theorem.  The adjacent supplier must carry the oriented
   Figure-2-4 path provenance; a pure-Gram `hV_figPath_closure` is too lossy
   for the oriented scalar packet.
   No mixed implementation is allowed: an oriented representative cannot feed
   `OS45OneBranchScalarGramEqPacket`, and a pure-Gram source packet cannot be
   justified from proper-complex determinant-`1` invariance alone.

   The latest blueprint correction rejects the earlier real-environment seed
   formulation.  At the OS45 horizontal edge the point
   `sourceMinkowskiGram d n (Q.symm (realEmbed (os45CommonEdgeRealPoint β x)))`
   is generally a complex quarter-turn scalar point, not
   `sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)`.  Therefore
   the seed cannot be stated as direct equality on a real Minkowski Gram
   environment.  The proof must instead use the OS §4.5 order:
   `BHW.os45AdjacentSPrimeScalarSeed_of_compactWickPairingEq` obtains a
   connected nonempty relatively open scalar seed in `S'_n` in two explicit
   steps.  First
   `BHW.os45AdjacentSPrimeSourceEq_of_compactWickPairingEq` proves equality
   on a connected complex source-neighborhood `Usrc`, using the checked
   compact Wick equality
   `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`, the
   Wick-section identity principle, and the explicit OS-I §4.5 adjacent
   source-chart scalarization theorem
   `BHW.os45AdjacentSPrimeScalarizationChart_of_figure24`, which puts
   `sourceMinkowskiGram '' Usrc` inside the adjacent double scalar domain,
   identifies the identity `hRep.Phi` pullback pointwise with the identity
   OS-II Wick branch, identifies the adjacent `hRep.Phi` pullback with the
   adjacent OS-II Wick branch only in compact pairings, and shrinks around the
   selected base point `x0` so `x0 ∈ V0`.  Its identity branch reduction is the ordinary
   forward-tube `branch_eq`/`extendF_eq_on_forwardTube` argument; its adjacent
   branch reduction is exactly
   `BHW.os45AdjacentWickTrace_sourceScalarRepresentative_pairing_eq_of_figure24`,
   not an adjacent raw-Wick forward-tube argument.  In the
   compact-Wick-to-pointwise step, continuity is needed only for the two
   scalarized source pullbacks.  Obtain it by composing the differentiable
   scalar pullbacks with
   `BHW.continuous_wickRotateRealConfig` using Mathlib
   `ContinuousOn.comp'` and the explicit `MapsTo` proof
   `fun x hx => hwick_mem x hx`.  The integral equality for those scalar
   pullbacks is the chain: canonical-lift Hall-Wightman boundary theorem,
   source-pullback/raw Figure-2-4 rewrites by `hRep.branch_eq` and Lorentz
   normalization, checked compact Wick equality, and the identity pointwise scalarization
   rewritten under the
   integral.  The proof must not silently use continuity of unrelated total
   `bvt_F` values off the Wick section, and must not use
   `ContinuousOn.comp_continuous` unless the
   chart has been changed to a global Wick-image statement.  The checked
   compact Wick equality is called with
   `ρ = 1`, so its swapped-order hypothesis is labelled by
   `(Equiv.swap i ⟨i.val + 1, hi⟩).symm * 1`; normalize this to the local
   adjacent transposition `τ` with `Equiv.swap_inv` and `mul_one` before
   passing `hV_swap_ordered`.  Then a complex regular point is chosen near the Wick
   source point for `x0` by `BHW.dense_sourceComplexGramRegularAt`, and scalar coordinates are
   extracted with the all-arity connected local-image packet
   `BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular_allArity`;
   in the hard range this is the checked
   `BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`,
   while in the easy range it uses the checked full symmetric-coordinate
   identification of the source variety.  The path provenance needed by the
   corridor is packaged in
   `BHW.os45AdjacentSPrimeSeedFigure24Path_of_compactWickPairingEq`, whose
   extra output is anchored at the same selected base point `x0`: the scalar
   seed theorem records a distinguished `Gseed ∈ Wseed`, the source chart
   supplies a path from `Gseed` to
   `sourceMinkowskiGram d n (fun k => wickRotatePoint (x0 k))`, and
   the selected Figure-2-4 source patch supplies the path-stability field
   `hV_figPath_closure`, recorded on `closure V` because the branch source germ is
   required at every point of the compact edge closure.  That field is the
   actual Streater-Wightman Figure-2-4
   configuration-level path from the Wick configuration to the OS45
   quarter-turn configuration, together with a second continuous
   ordinary-extended-tube realization of the adjacent permuted Gram point.
   The provenance form must keep
   `Gseed_def : Gseed = sourceMinkowskiGram d n zreg`; the path proof should
   either `subst Gseed` and then define
   `γseed : Path (sourceMinkowskiGram d n zreg)
   (sourceMinkowskiGram d n zwick0)`, or keep `Gseed` and cast the mapped
   source path along `Gseed_def`.  Defining `γseed : Path Gseed ...` after
   `subst Gseed` is not Lean-shaped.  Without this field the scalar-only seed
   has lost the endpoint needed by `Path.trans`.
   The selected source patch must also export the open-chart canonical lift
   field `hV_adjLift_ET` for this same rotated realization; that field feeds
   the source-pairing theorem, while `hV_figPath_closure` feeds the later
   scalar path.  Its adjacent branch is the Figure-2-4 two-plane rotated
   realization from the checked `AdjacentOverlapWitness.lean` model, made
   uniform around the same equal-time Figure-2-4 anchor by a compact-open shrink over
   `unitInterval`; it is not the bare relabelled path `Γ t ∘ τ`.  The ordered
   seed is chosen only afterward inside `Ufig ∩ Upath`, and the final
   precompact `V` is then shrunk inside the ordered-sector preimages.  The
   blueprint now pins the support names:
   `BHW.os45Figure24IdentityPath`,
   `BHW.figure24RotateAdjacentConfig`,
   `BHW.figure24RotateAdjacentConfig_lorentz_inverse`, and
   `BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability`, whose
   projections include `BHW.swFigure24_adjacentHorizontalRealEnvironment` and
   `BHW.swFigure24_adjacentPathStableNeighborhood_exists`.  The support
   theorem feeding the path-stability neighborhood must also export
   `realEmbed xrot = figure24RotateAdjacentConfig hd
     (realEmbed (fun k => xfig (τ k)))`; otherwise the compact-open
   path-stability proof has no identified base point.  Its proof transcript
   now fixes the actual arithmetic: the identity path uses
   `0 < 1 - (t : ℝ) / 2` for `t : unitInterval`, while the rotated adjacent
   witness has first-axis consecutive differences `2 / 5` at `i`, `1 / 5` at
   `i + 1`, and `(3 / 5) * Δe1` on all other gaps.  Thus the adjacent path
   support is anchored in the checked `(3,4,5)` rotation calculation, not in a
   vague strict-inequality claim.  The only new generic helper on this
   subroute is the finite-subcover tube lemma
   `BHW.exists_open_nhds_forall_mem_of_compact_parameter`, and the Gram
   calculation uses the genuine scalar-product theorem
   `BHW.sourceMinkowskiGram_complexLorentzAction` plus
   `BHW.sourceMinkowskiGram_perm`, with `Equiv.swap_inv` normalizing the
   adjacent transposition inverse from `τ.symm` to `τ`.  The optional theorem
   `BHW.swFigure24_wickToQuarterTurn_doubleETRealizationPath` is only a
   projection from `hV_figPath_closure`, not an independent broad theorem about an
   arbitrary real-open `V`; its theorem surface should not retain the ordered,
   Jost, or horizontal-edge hypotheses already consumed by the producer of
   `hV_figPath_closure`.  The scalar theorem
   `BHW.swFigure24_wickToQuarterTurn_scalarPath` is then only the mechanical
   corollary `γ t = sourceMinkowskiGram d n (Γ t)`, with double-domain
   membership proved by
   `BHW.mem_sourceDoublePermutationGramDomain_iff_exists_realizations`.
   This correction is mandatory: do not assert the scalar path directly, and
   do not claim that the adjacent relabelling of `Γ t` itself lies in the
   ordinary forward tube.  Its paper source is the local OCR of
   `references/pct-spin-and-statistics-and-all-that-9781400884230_compress.pdf`
   around printed page 73: the adjacent transposition `P(j,j+1)` and Figure
   2-4 give a common real Jost environment for the ordinary and adjacent
   permuted extended tubes;
   `BHW.os45AdjacentQuarterTurnScalarCorridor_of_figure24` supplies the
   Hall-Wightman/BHW connected scalar corridor from that seed to the selected
   OS45 quarter-turn scalar neighbourhood by the Figure-2-4 scalar path and
   the finite-dimensional topology theorems
   `BHW.sourceComplexGramVariety_local_connectedRelOpen_basis` and
   `BHW.sourceComplexGramVariety_connectedRelOpenTube_around_compactPath`.
   The corridor assembly is now checked in
   `OSToWightmanLocalityOS45TraceMembership.lean`: after the path `γ` is
   supplied, it thickens `γ` by the connected source component, rewrites the
   adjacent ACR edge through
   `BHW.os45CommonEdgeRealPoint_adjacent_swap_eq`, and pulls the final scalar
   tube back through `z ↦ sourceMinkowskiGram d n (Q.symm z)` while intersecting
   the checked OS45 ACR and pulled BHW branch domains.
   Equality propagation along that corridor is now checked in the generic
   source theorem `BHW.os45AdjacentScalarEq_on_quarterTurnCorridor` in
   `BHWPermutation/SourceComplexDensity.lean`; it is deliberately generic in
   the represented function `F`, so the local theorem depends only on
   `SourceScalarRepresentativeData` and the source-variety identity principle,
   not on unrelated upstream `bvt_F` proof obligations.
   The singular Schur branch of the local-basis theorem uses the explicit
   rank-`<=` cone package
   `BHW.matrixSymmetricRankLECone_small_connected`,
   `BHW.isConnected_sourcePrincipalSchurGraph_rankLE_image`, and
   `BHW.sourcePrincipalSchurGraph_rankLE_image_eq_openCoordinatePatch`; it is
   not allowed to reuse the checked rank-exact cone theorem as if the
   lower-rank source variety were rank-exact;
   and
   `BHW.os45AdjacentScalarEq_on_quarterTurnCorridor` propagates equality by
   the source-variety identity theorem.  No real-edge `extendF` equality,
   `AdjacentOSEOWDifferenceEnvelope`, final `bvt_W` locality, or global PET
   branch-independence is allowed in these upstream source suppliers.

   The generic arbitrary-`β` theorem is not licensed as a standalone
   production source theorem until the same `S'_n` seed and BHW corridor are
   proved for arbitrary `β`; on the active theorem-2 path it should be
   implemented only as an assembly lemma consuming
   `BHW.OS45OneBranchScalarGramEqPacket`.  The
   public scalar suppliers are
   `BHW.os45OneBranchScalarGramEq_sourceInput_id` for `β = 1` and
   `BHW.os45OneBranchScalarGramEq_sourceInput_adjacent` for the adjacent
   swap; any generic helper is private assembly from an already constructed
   scalar corridor.  The identity supplier must reduce
   `sourceDoublePermutationGramDomain d n 1` by the explicit helper
   `BHW.sourceDoublePermutationGramDomain_one_eq`, proved by unfolding
   `sourceDoublePermutationGramDomain` and using
   `BHW.sourcePermuteComplexGram_one`; do not rely on an unstated
   "definitional" simplification of the double-domain field.  The adjacent
   supplier must carry the selected
   oriented Figure-2-4 path field on its theorem surface.  The higher
   `BHW.os45BranchHorizontalOrientedSourceGermAt_of_figure24_adjacent`
   supplier therefore carries `hV_orientedPath_closure`; for each
   `x ∈ closure V` it passes the corresponding path as the oriented
   Figure-2-4 provenance.  Without that input, the OS45
   quarter-turn scalar point has not been connected to the `S'_n` seed inside
   the adjacent oriented double scalar domain, and the theorem would again be trying to
   infer scalar branch agreement from domain membership.  The closure-point
   suppliers must also choose a fresh local open patch around each
   `x ∈ closure V`; they must not pass the original open `V` to a scalar input
   theorem when only `x ∈ closure V` is known.  The local patch is the finite
   intersection of `Ufig`, the identity and swapped ordered-sector preimages,
   and the relevant horizontal pulled-domain preimage.  In the adjacent case,
   this local original-coordinate patch supplies the scalar packet at `y0`; the
   source-germ assembly step separately transports to the relabelled patch
   `Uτ := {u | (fun k => u (τ k)) ∈ Ux}` and rewrites the scalar packet along
   `BHW.os45CommonEdgeRealPoint_adjacent_swap_eq` before calling
   `BHW.os45BranchHorizontalSourceGermAt_of_orientedSourceEq`.  This
   preimage definition is equivalent to `{u | ∃ v ∈ Ux, u = fun k => v (τ k)}`
   for an adjacent swap, but it makes openness and basepoint membership
   Lean-direct.  The proof must explicitly transport all five one-branch
   source-patch fields across this finite permutation: openness, Jost membership,
   branch-`τ` ordered membership, ordinary extended-tube membership of the
   relabelled configuration, and horizontal pulled-BHW membership after the
   common-edge rewrite.  The basepoint proof is
   `change (fun k => xτ (τ k)) ∈ Ux; simpa [xτ, τ] using hxUx`; it is not
   automatic from the original `Ux` membership unless this relabelling step is
   performed.  The theorem-2 blueprint now records the checked tactic-shaped
   transport: `hUτ_open` is `hUx_open.preimage` along the continuous finite
   permutation map; `hUτ_jost` applies `BHW.jostSet_permutation_invariant` to
   `v := u ∘ τ`; `hUτ_ordered` consumes the swapped ordered field of `Ux`;
   `hUτ_ET` consumes the adjacent ordinary-ET field; and `hUτ_horiz` rewrites
   `os45CommonEdgeRealPoint τ u` to `os45CommonEdgeRealPoint 1 v` by
   `BHW.os45CommonEdgeRealPoint_adjacent_swap_eq`.
   The selector construction must choose the ordered seed inside
   `Ufig ∩ Upath`, where `Upath` is the Figure-2-4 compact-open
   path-stability neighborhood around the same equal-time witness returned
   with `Ufig`; this shared anchor is what makes both the open-chart
   `hV_adjLift_ET` field and the closure-level `hV_figPath_closure` field
   legitimate.  The `Upath` canonical-lift field is unconditional on `V` once
   `closure V ⊆ Upath`; the full `Γ, Δ` closure path additionally uses
   `hV_ordered_closure` to keep the identity path in the ordinary extended
   tube up to the quarter-turn endpoint.  The implementation must not call two
   independent existential theorems for `Ufig` and `Upath` and then assume the
   witnesses agree.
4. The compact common-germ theorem `BHW.os45BranchHorizontalCommonGerm` then
   glues these branch-specific germs over `closure E`; the identity and
   adjacent germs remain different branch packets.
5. The branchwise BV construction gives `Tid` and `Tτ`; only after subtracting
   those packets may `SCV.chartDistributionalEOW_local_envelope` be invoked.
   The subsequent side-component gluing is fixed in those same one-chart
   coordinates: choose `ys` with `∑ j, ys j = η₁`, shrink the selected patch
   so `(SCV.localEOWRealLinearCLE ys hli).symm (η(x))` is coordinatewise
   positive, and define the side components from
   `Ωplus ∩ SCV.ChartPositiveOrthant m` and
   `Ωminus ∩ SCV.ChartNegativeOrthant m`.  Then the local ball overlaps are
   exactly `SCV.StrictPositiveImagBall R` and
   `SCV.StrictNegativeImagBall R`, so the side identities returned by the
   checked one-chart theorem are already the full overlap equalities needed
   for holomorphic gluing; the exact rewrites are the pure topology lemmas
   `SCV.ball_inter_positiveOrthantComponent_eq_strictPositiveImagBall` and
   `SCV.ball_inter_negativeOrthantComponent_eq_strictNegativeImagBall`.
   The finite Wick/real trace membership in those components is reduced to
   the generic helper `SCV.path_endpoint_mem_connectedComponentIn` plus the
   explicit OS45 positive/negative path membership calculations.
   Openness and connectedness of the side components are supplied by
   `SCV.isOpen_connectedComponentIn_complexChart_of_isOpen` and
   `SCV.isConnected_connectedComponentIn_of_mem` from finite-dimensional
   local connectedness and the standard connected-component-in API.
   Disjointness of the positive/negative side components uses the nonzero
   chart dimension through
   `SCV.disjoint_chartPositiveOrthant_chartNegativeOrthant`; do not omit
   `hm : 0 < m`, since the zero-dimensional orthant predicates are vacuous.
   The final holomorphic gluing theorem is
   `SCV.glue_localEnvelope_to_disjoint_sideComponents`, and its output domain
   is part of the contract: it returns `U = U0 ∪ Uplus ∪ Uminus`, not an
   unnamed larger set.  Its proof uses the pure topology helper
   `SCV.isConnected_threeUnion_of_connected_core_meets`, then proves the
   three local `EqOn` facts for the nested-if glued function and combines
   local holomorphy by `DifferentiableOn.congr` plus two applications of
   `DifferentiableOn.union_of_isOpen`.
   Do not replace this by a broad
   original-coordinate linear sign condition; that would reintroduce an
   unproved identity-theorem obligation on arbitrary overlap components.
6. The scalar theorem `BHW.os45AdjacentScalarGerm_of_OSII_Figure24` is
   downstream only.  It may be proved after
   `BHW.os45_adjacent_commonBoundaryEnvelope` and
   `bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`
   have produced real-edge equality.  It is an audit/export of the EOW result,
   not an input to the source suppliers.

The theorem-2 local source route is now a Lean-facing implementation contract
for the named support theorems above.  The previous circular dependence on
the downstream scalar germ has been retired; implementation must still proceed
in the documented order and may not skip ahead to local EOW, global PET branch
independence, or final `bvt_W` locality.

The Figure-2-4 source-selector support packet is now checked; it was the first
allowed Lean pass after the earlier source-route correction.  Its file/order
contract remains fixed for audit purposes: publicize only the
concrete Figure-2-4 witness export
`BHW.figure24_adjacentTwoPlaneRotationSupport` from
`ComplexLieGroups/AdjacentOverlapWitness.lean`; the public axes
`BHW.figure24Axis1`, `BHW.figure24Axis2`, and the finite formula
`BHW.figure24RotateAdjacentConfig` also live there, as does
`BHW.figure24RotateAdjacentConfig_lorentz_inverse`, so the witness export and
the scalar path proof do not depend on the OS45 companion's path topology.
This algebraic export is now checked.  The generic compact parameter tube
lemma, the OS45 identity path, the zero-time identity-path lemma, joint
identity-path continuity, rotation continuity, composed rotated-path
continuity, Lorentz-invariance scalar identity, and
`BHW.swFigure24_adjacentPathStableNeighborhood_exists` are also checked in the
small OS45 Figure-2-4 companion file.  The checkpoint also checked
`BHW.swFigure24_adjacentHorizontalEnvironmentWithPathStability` and
`BHW.os45_adjacent_identity_horizontalEdge_sourcePatch`.  The next live work is
therefore the proof-doc-only scalar-source route above, not another
Figure-2-4 selector theorem.  Any theorem that
claims the bare adjacent relabelling of the identity path is forward-tube
valued is off route; the adjacent certificate is the rotated Figure-2-4
extended-tube realization.

## 0. Paper-authority rule

Every proof doc and production implementation must follow the OS papers
strictly.  OS II is the authoritative correction for the `E -> R` analytic
continuation, growth, and tempered boundary-value route wherever OS I depended
on Lemma 8.8.  The only currently documented OS-paper error is OS I Lemma 8.8;
all other deviations require a new local paper audit entry before they can
affect theorem surfaces or implementation.

Allowed "fill-in" work is limited to:

1. spelling out paper steps as Lean theorem packages;
2. adding standard analytic/topological lemmas needed to formalize those paper
   steps;
3. replacing the false OS I Lemma 8.8 many-variable jump with the OS II Chapter
   V/VI induction and estimate machinery.

Not allowed:

1. alternate proof routes chosen for implementation convenience;
2. theorem surfaces that weaken or strengthen the OS statement without a paper
   reason;
3. generic infrastructure shortcuts that bypass an OS-paper step;
4. same-test Euclidean/Minkowski equalities unless an explicit proved bridge
   justifies that exact surface.

## 0.1. External-theorem circularity audit

Before any external theorem is accepted as a theorem-2 input, audit the proof of
that external theorem for direct or transitive dependence on local
commutativity, weak local commutativity, or any equivalent permutation
symmetry of the Wightman boundary distributions being proved.

If such a dependence is present, the theorem is circular for theorem 2 and must
be fenced off as orientation only.  It may not be used as a proof supplier even
if its conclusion has the right shape.

Current examples:

1. `blocker_iterated_eow_hExtPerm_d1_nontrivial` is not a theorem-2 input in
   dimension one because it assumes the already-proved adjacent locality
   predicate (`IsAdjacentLocallyCommutativeWeak 1 W` after the API
   clarification).
2. Streater-Wightman Theorem 3-6 is not a theorem-2 input because its proof
   uses local commutativity.
3. Streater-Wightman Figure 2-4 remains allowed only as adjacent geometric
   real-environment input, because that local geometry does not use QFT
   locality.
4. `hallWightman_fixedPoint_endpointActiveGallery_of_two_le` is no longer an
   active theorem-2 frontier in its documented form. Its edge relation requires
   common fixed-`w` permuted-forward-tube witnesses, but the repository proves
   that distinct permuted forward-tube sectors are disjoint. The hF_perm-only
   generic direct BHW source branch-law theorem
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`
   is also not ready to close as stated.  The approved Deep Research audit
   found the statement mathematically unsafe: because nontrivial permuted
   forward tubes are disjoint from the ordered forward tube, total Lean values
   of `F` off the ordered tube can satisfy `hF_perm` without constraining the
   analytic germ whose BHW continuation is being compared.  The active
   replacement is the source-backed Hall-Wightman/BHW compatibility theorem:
   selected adjacent OS/Jost data supply
   `BHW.SourceDistributionalAdjacentTubeAnchor`, and the source theorem proves
   single-valued continuation on `S''_n`.  The checked lower-layer BHW/PET
   monodromy interface remains useful conditional infrastructure, but the
   reachable-label `hOrbit` theorem is an extra pointwise orbit-stratification
   statement and is not the immediate theorem-2 implementation frontier.  The
   genuine remaining BHW geometry frontier is the scalar-product source
   overlap and cover-reaching proof in
   `BHWPermutation/SourceExtension.lean`;
   `BHWPermutation/PermutationFlow.lean` is still forbidden as a theorem-2
   source theorem because its current top-level BHW theorem depends on the
   adjacent locality predicate.
   A checked false shortcut has been ruled out: pointwise permutation symmetry
   of the raw base function does not by itself compare arbitrary PET sector
   branches, because the complex-Lorentz representative needed for the
   comparison need not stay in the base forward tube.  The remaining gap is
   exactly Hall-Wightman single-valued continuation for the distributionally anchored
   symmetric permuted-tube datum.  The theorem-2 blueprint now fixes the internal
   branch-law proof contract: make the branches
   `G π z = BHW.extendF F (fun k => z (π k))` explicit, obtain their sector
   holomorphicity from
   `BHW.permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz`, build
   the symmetric `S'_n` datum using the distributional Euclidean/Jost anchor, apply the source
   Hall-Wightman/BHW compatibility theorem on `S''_n`, and only then build
   one `Fpet` by the existing `BHW.gluedPETValue` API.  The blueprint now also fixes
   the private lemma ladder for the implementation pass:
   `source_permutedForwardBranch_holomorphicOn`,
   `source_permutedForwardBranch_restrictedLorentzInvariant`,
   `source_permutedForwardBranch_symmetric`, and exactly one non-elementary
   source-facing compatibility theorem
   `hallWightman_source_permutedBranch_compatibility`.  No helper may assume
   the `S''_n` compatibility that this source theorem is meant to prove.
   The Lean surface now also includes the data-carrying
   `SelectedAdjacentDistributionalJostAnchorData` packet and the checked
   reindexing definition
   `bvt_F_distributionalJostAnchor_of_selectedJostData` in
   `OSToWightmanSelectedWitness.lean`; that bridge introduces no new `sorry`
   and supplies `BHW.SourceDistributionalAdjacentTubeAnchor` from selected
   adjacent OS anchor data.
   The source side also now has checked full-matrix sufficient theorems
   `BHW.sourceDistributionalUniquenessSet_of_isOpen_nonempty` and
   `BHW.sourceDistributionalUniquenessSet_of_contains_open`: a nonempty open
   real set in the full product coordinate space is a uniqueness set for
   holomorphic scalar-product representatives, by the repo's totally-real
   identity theorem.  These lemmas are true but not the general OS supplier.
   The attempted theorem that the Gram image of an OS45 Jost patch contains a
   full-matrix open subset is false: Gram matrices are symmetric, and in
   arity above the spacetime vector dimension they lie in a rank-bounded
   Hall-Wightman scalar-product variety.  The API-backed Deep Research check
   `v1_ChYtLURyYWZ4UjFKNy00d19TbWNMUUJnEhYtLURyYWZ4UjFKNy00d19TbWNMUUJn`
   confirmed this correction; the production anchor now carries the
   variety-level predicate `BHW.sourceDistributionalUniquenessSetOnVariety`.
   The approved Deep Research check rejected the hF_perm-only source boundary
   and routed growth/temperedness to the upstream OS-II boundary-value
   construction.  The remaining implementation step is now specified down to
   Lean pseudocode: prove or source-import
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
   from Hall-Wightman's scalar-product theorem plus distributional EOW on the
   distributionally anchored symmetric permuted-tube datum `S'_n`, using
   `sourceMinkowskiGram`, branch scalar-product representatives,
   compact-test Schwinger symmetry on adjacent permutation-indexed Jost
   patches, branch-boundary distribution matching there, scalar-product
   uniqueness, and Hall-Wightman single-valued continuation on `S''_n`.  Any
   adjacent-patch cover connectivity used internally belongs inside that source
   theorem, not in the theorem-2 consumer API.  A common pointwise `Φ` may be
   produced as a corollary after this source theorem, but it is not the OS
   input.  The follow-up Deep Research check
   `v1_ChdUSW5yYWFuUkhNNlVfdU1QOE9YaGtRWRIXVElucmFhblJITTZVX3VNUDhPWGhrUVk`
   specifically rejects promoting
   `BHW.petSectorFiber_adjacent_connected_of_two_le` to an active theorem-2
   gate.
   The corrected OS supplier now has an implementation-level decomposition:
   `E` should be the whole Gram image of the selected OS45 patch, while
   uniqueness is proved by finding a smaller regular Hall-Wightman real
   environment inside that image and applying the checked monotonicity lemma
   `BHW.sourceDistributionalUniquenessSetOnVariety_mono`.  This OS-supplier
   Gram-environment layer is now checked in
   `BHWPermutation/SourceDistributionalUniqueness.lean` as
   `sourceDistributionalUniquenessSetOnVariety_of_open_jost_patch` and
   `exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch`: a
   nonempty open Jost patch has a Gram image which is a variety-level
   uniqueness environment.  The regular-stratum
   definitions themselves are now checked in Lean:
   `sourceGramExpectedDim`, `sourceConfigurationSpan`,
   `sourceComplexConfigurationSpan`, `SourceGramRegularAt`, and
   `SourceComplexGramRegularAt`, together with the concrete template
   `sourceFullSpanTemplate`.  The algebraic tangent support is also now
   checked in Lean: `sourceRealGramDifferential`,
   `sourceComplexGramDifferential`,
   `sourceRealMinkowskiGram_hasFDerivAt`,
   `contDiff_sourceRealMinkowskiGram`,
   `sourceSelectedGramCoord`, `sourceSelectedSymCoordSubspace`,
   `linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero`,
   `span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero`,
   `sourceRealGramDifferential_symm`,
   `sourceSelectedGramCoord_differential_mem`,
   `minkowskiInner_dualVectorOfLinearFunctional`,
   `exists_minkowski_dual_family_of_linearIndependent`,
   `exists_minkowski_dual_sourceRows_of_sourceRegularMinor_ne_zero`,
   `sourceRealGramDifferential_apply_eq_minkowskiInner`,
   `minkowskiInner_sum_smul_dual_left`,
   `sourceMinkowskiInner_sum_smul_left`,
   `sourceMinkowskiInner_sum_smul_right`,
   `sourceMinkowskiInner_add_right`,
   `sourceMinkowskiInner_smul_right`,
   `sourceMinkowskiInner_left_nonDegenerate`,
   `sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family`,
   `sourceSelectedGramCoord_comp_differential_range_eq`,
   `sourceRows_coefficients_of_sourceRegularMinor_ne_zero`,
   `sourceRealMinkowskiGram_apply_eq_minkowskiInner`,
   `sourceSelectedIndex_surjective_of_le`,
   `sourceSelectedRows_span_top_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero`,
   `sourceRealGramMap_constant_on_selectedVerticalFibers`,
   `sourceRealGramDifferential_eq_zero_of_selectedGramCoord_eq_zero`,
   `sourceSelectedGramCoord_injective_on_differential_range`,
   `sourceSelectedGramDifferentialToSym`,
   `sourceSelectedRealGramMap`,
   `sourceSelectedRealGramMap_hasStrictFDerivAt`,
   `sourceSelectedGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedGramDifferentialToSym_ker_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedRealGramMap_implicit_chart_of_nonzero_minor`,
   `sourceSelectedUpperPair`, `sourceSelectedSkewCoord`,
   `sourceSelectedSkewCoord_ker`, `sourceSelectedSkewCoord_surjective`,
   `card_sourceSelectedUpperPair`, `finrank_sourceSelectedSymCoordSubspace`,
   `sourceRealGramDifferential_rank_of_exists_nonzero_minor`,
   `sourceRealGramDifferential_rank_of_regular`,
   `sourceComplex_regular_of_real_regular`,
   `sourceComplexGramDifferential_realEmbed`,
   `sourceRealGramTangentSpaceAt`, `sourceComplexGramTangentSpaceAt`,
   `SourceComplexifiedRealTangentEqualsComplexTangent`, and
   `IsHWRealEnvironment`.  The tangent-complexification support theorem
   `sourceComplexGramDifferential_realEmbed_range_eq_complex_span` is now
   checked too: at a real source point, the complex differential range is the
   complex span of the real differential range.  The maximal-totally-real
   tangent packet is now checked in
   `BHWPermutation/SourceComplexTangent.lean`: it proves the easy tangent
   inclusions, complex selected-row span transfer, shared real coefficient
   expansion, selected Schur-complement differential formula, complex selected
   differential surjectivity by real/imaginary splitting, the hard theorem
   `sourceComplexGramTangent_subset_realEmbed_range_of_regular`, and
   `sourceComplexifiedRealTangentEqualsComplexTangent_of_regular`.  The local
   Hall-Wightman real-environment supplier
   `sourceRealGramMap_realEnvironmentAt_of_regular` is also checked: it shrinks
   a prescribed source neighborhood by `JostSet`, uses the checked relative-open
   source Gram image theorem, and fills `IsHWRealEnvironment` with Jost
   realizers and the new maximal-totally-real tangent theorem.  The
   regular-locus
   template/minor support is now
   checked too: `sourceTemplateDomainIndex`, `sourceTemplateCoordIndex`,
   `sourceTemplateDomainIndex_injective`,
   `sourceTemplateCoordIndex_injective`,
   `sourceFullSpanTemplate_basisVector`,
   `linearIndependent_sourceFullSpanTemplate_basisBlock`,
   `sourceFullSpanTemplate_regular`, `sourceRegularMinor`,
   `continuous_sourceRegularMinor`,
   `exists_nonzero_coordinate_minor_of_linearIndependent`,
   `sourceGramRegularAt_of_exists_nonzero_minor`,
   `exists_nonzero_minor_of_sourceGramRegularAt`, and
   `sourceGramRegularAt_iff_exists_nonzero_minor`, plus openness of the
   regular locus as `isOpen_sourceGramRegularAt` and the canonical template
   minor facts `sourceFullSpanTemplate_regularMinor_eq_one` and
   `sourceFullSpanTemplate_regularMinor_ne_zero`, plus the determinant-line
   density package `sourceCanonicalRegularMinorLinePolynomial`,
   `sourceCanonicalRegularMinorLinePolynomial_leadingCoeff`,
   `sourceCanonicalRegularMinorLinePolynomial_ne_zero`,
   `sourceCanonicalRegularMinorLinePolynomial_eval`,
   `sourceCanonicalRegularMinor_nonzero_dense`, and
   `dense_sourceGramRegularAt`.  The post-cleanup rank-stage support now lives
   in the small companion module `BHWPermutation/SourceRegularRank.lean`,
   rather than further growing `SourceExtension.lean`.  The theorem-2
   blueprint also gives proof skeletons for the three supplier facts:
   maximal-span density/open regular locus via determinant minors, regular
   Gram-map rank/local real-environment via the explicit selected-coordinate
   rank theorem and a selected-coordinate constant-rank chart for the finite
   source Gram map, and Hall-Wightman real-environment uniqueness via local
   maximal-totally-real selected-coordinate charts plus analytic continuation on
   the irreducible scalar-product variety.  These supplier facts are now
   checked and consumed by the open-Jost-patch uniqueness theorem under the
   legacy strong API.  The analytic bookkeeping lemma
   `SourceVarietyHolomorphicOn.sub` is checked in `SourceExtension.lean`; the
   corrected scalar-source route now also has the parallel checked germ lemma
   `SourceVarietyGermHolomorphicOn.sub`.  The complex selected-coordinate
   local-IFT substrate
   is also checked in `SourceComplexChart.lean`
   (`contDiff_sourceMinkowskiGram`,
   `sourceMinkowskiGram_hasFDerivAt`,
   `sourceSelectedComplexSymCoordSubspace`,
   `sourceSelectedComplexGramDifferentialToSym`,
   `sourceSelectedComplexGramMap`,
   `sourceSelectedComplexGramMap_hasStrictFDerivAt`,
   `sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedComplexGramMap_implicit_chart_of_nonzero_minor`,
   `sourceSelectedSymCoordKey`,
   `sourceSelectedComplexSymCoordKeyEquiv`,
   `sourceSelectedRealSymCoordKeyEquiv`,
   `sourceSelectedSymCoordRealComplexify`,
   `sourceSelectedComplexSymCoordKeyEquiv_real_slice`,
   `sourceSelectedComplexSymCoordFinEquiv`,
   `sourceSelectedRealSymCoordFinEquiv`,
   `sourceSelectedComplexSymCoordFinEquiv_real_slice`,
   `sourceComplexRegularMinor`,
   `continuous_sourceComplexRegularMinor`,
   `sourceComplexRegularMinor_realEmbed`,
   `exists_nonzero_complex_coordinate_minor_of_linearIndependent`,
   `sourceComplexGramRegularAt_of_exists_nonzero_minor`,
   `exists_nonzero_minor_of_sourceComplexGramRegularAt`,
   `sourceComplexGramRegularAt_iff_exists_nonzero_minor`,
   `isOpen_sourceComplexGramRegularAt`,
   `linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero`,
   `span_sourceComplexRows_eq_sourceComplexConfigurationSpan_of_sourceComplexRegularMinor_ne_zero`,
   `sourceSelectedComplexRows_span_top_of_sourceComplexRegularMinor_ne_zero`,
   `sourceComplexStdBasis_sum`,
   `sourceComplexMinkowskiDualVectorOfLinearFunctional`,
   `sourceComplexMinkowskiInner_dualVectorOfLinearFunctional`,
   `exists_sourceComplexMinkowski_dual_family_of_linearIndependent`,
   `exists_sourceComplexMinkowski_dual_sourceRows_of_sourceComplexRegularMinor_ne_zero`,
   `sourceComplexMinkowskiInner_sum_smul_dual_left`,
   `sourceSelectedComplexGramCoord_comp_differential_range_eq_of_sourceComplexRegularMinor_ne_zero`,
   `sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero`,
   `sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor`,
   `sourceComplexRows_coefficients_of_sourceComplexRegularMinor_ne_zero`,
   `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop`,
   `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero`,
   `sourceComplexGramMap_constant_on_selectedVerticalFibers`,
   `sourceComplexGramMap_localRelOpenImage_in_open_of_complexRegular`,
   `sourceSelectedComplexRows_span_top_of_selectedComplexGramCoord_eq_regular`,
   `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety`,
   `sourceComplexGramMap_localRelOpenImage_in_open_of_realRegular`,
   `contDiff_sourceSelectedComplexGramMap_of_injective`,
   `sourceSelectedComplexGramKernelProjection`,
   `sourceSelectedComplexGramKernelProjection_apply_ker`,
   `sourceSelectedComplexGramProdMap`,
   `contDiff_sourceSelectedComplexGramProdMap`,
   `sourceSelectedComplexGramProdMap_hasFDerivAt`,
   `sourceSelectedComplexGramProdMap_fderiv`,
   `sourceSelectedComplexGramProdMap_base_fderiv_isInvertible`,
   `sourceSelectedComplexGramProdMap_local_invertible_nhds`,
   `sourceSelectedComplexGramImplicitChart`,
   `sourceSelectedComplexGramImplicitChart_apply`,
   `sourceSelectedComplexGramImplicitChart_mem_source`,
   `sourceSelectedComplexGramImplicitChart_self`,
   `sourceSelectedComplexZeroKernelTargetCLM`,
   `sourceSelectedComplexZeroKernelTargetCLM_apply`,
   `sourceSelectedComplexGramZeroSection_differentiableOn`,
   `sourceSelectedComplexGramZeroSection_selectedGram`,
   `sourceSelectedComplexGramZeroSection_base`,
   `sourceSelectedComplexGramFlatCoordCLM`,
   `sourceSelectedComplexGramFlatCoordCLM_apply`,
   `sourceSelectedComplexGramFlatCoordCLM_source`,
   `sourceSelectedComplexGramCoord_eq_of_flatCoord_eq`,
   `sourceSelectedComplexGramZeroSection_image_eq_flatCoord_preimage`,
   `sourceSelectedComplexGramZeroSection_image_relOpen`,
   `sourceSelectedComplexGramZeroSection_gram_differentiableOn`,
   `exists_sourceSelectedComplexGramZeroSection_good_ball`,
   `sourceSelectedComplexSymCoordFinEquiv_symm_real_slice`,
   `sourceSelectedRealGramImplicitChart`,
   `sourceSelectedRealGramImplicitChart_mem_source`,
   `sourceSelectedRealGramImplicitChart_self`,
   `sourceSelectedRealGramImplicitChart_fst`,
   `sourceSelectedRealZeroKernelTargetCLM`,
   `sourceSelectedRealZeroKernelTargetCLM_apply`,
   `sourceSelectedRealGramZeroSection_selectedGram`,
   `sourceSelectedRealGramZeroSection_base`,
   `sourceSelectedRealGramZeroSection_continuousOn`,
   `sourceSelectedComplexGramZeroSection_real_slice_gram`,
   `exists_sourceSelectedRealGramZeroSection_good_ball`,
   `sourceSelectedComplexGramBaseCoord_real_slice`,
   `sourceComplexGramVariety_selectedChart_of_realRegular`,
   `SourceVarietyGermHolomorphicOn.comp_differentiableOn_chart`,
   and `sourceVariety_localChart_totallyReal_zero` with the germ hypothesis,
   all sorry-free).  The global identity support has started with the checked
   Minkowski-to-dot reduction
   `complexMinkowskiToDotLinearEquiv`,
   `sourceComplexMinkowskiInner_eq_dot_after_equiv`,
   `sourceMinkowskiGram_eq_dotGram_after_equiv`, and
   `sourceComplexGramVariety_eq_dotGram_range` in
   `BHWPermutation/SourceComplexGlobalIdentity.lean`.  The remaining
   symmetric-space definitions and inclusions
   `sourceSymmetricMatrixSpace`, `sourceMatrixMinor`,
   `sourceSymmetricRankLEVariety`, `sourceComplexDotGram_symm`,
   `sourceComplexDotGram_mem_sourceSymmetricMatrixSpace`, and
   `sourceComplexGramVariety_subset_sourceSymmetricMatrixSpace` are checked
   there too.  The determinant/minor forward inclusion is now checked as
   `sourceComplexDotGram_minor_eq_zero`,
   `sourceComplexDotGram_mem_sourceSymmetricRankLEVariety`, and
   `sourceComplexGramVariety_subset_sourceSymmetricRankLEVariety`; the next
   diagonal square-root substep is checked as `complexSquareRootChoice`,
   `complexSquareRootChoice_mul_self`, and
   `sourceComplexDiagonal_factorization_self`.  The orthogonal-diagonalization
   spine is now also checked as `bilinform_orthogonal_basis_expansion`,
   `sourceMatrix_toBilin_isSymm`,
   `sourceSymmetricMatrix_exists_orthogonal_coordinate_expansion`,
   `sourceSymmetricMatrix_factorization_finrank`, and
   `sourceSymmetricMatrix_factorization_self`.  This proves the unrestricted
   complex symmetric `Z = A * Aᵀ` factorization in `n` coordinates.  The
   rank-compression theorem is now checked as
   `complex_symmetric_matrix_factorization_of_rank_le`, and the rank-defined
   reverse inclusion into the source variety is checked as
   `sourceComplexGramVariety_mem_of_symmetric_rank_le`.  The minor-to-rank
   bridge is now checked as `sourceMatrix_rank_le_of_minors_eq_zero`, with
   row/column extraction support
   `exists_linearIndependent_rows_of_rank_ge` and
   `exists_nondegenerate_square_submatrix_of_rank_ge`.  The converse rank-to-
   minor direction and rank-stratum API are checked as
   `matrix_rank_ge_of_nondegenerate_square_submatrix`,
   `sourceMatrix_minors_eq_zero_of_rank_le`,
   `sourceSymmetricRankLEVariety_eq_rank_le`,
   `sourceSymmetricRankExactStratum`, and
   `sourceSymmetricRankExactStratum_subset_rankLE`, with the positive-rank
   difference characterization
   `sourceSymmetricRankExactStratum_eq_rankLE_diff`.  Thus the full algebraic
   identification is checked as
   `sourceComplexGramVariety_eq_rank_le`, with stratum inclusion
   `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety` also
   checked.  The closedness/regular-locus topology needed for the singular
   closure stage is now also checked:
   `continuous_sourceMatrixMinor`, `isClosed_sourceSymmetricMatrixSpace`,
   `isClosed_sourceSymmetricRankLEVariety`,
   `isClosed_sourceComplexGramVariety`,
   `sourceComplexGramVariety_diff_lowerRank_eq_rankExact`, and
   `sourceSymmetricRankExactStratum_relOpenIn_sourceComplexGramVariety`.  The
   first Schur-complement regular-patch obstruction is checked as
   `matrix_rank_ge_card_of_nondegenerate_square_submatrix` and
   `schur_complement_entry_eq_zero_of_rank_le`: on an invertible principal
   block, rank at most the block size forces every Schur-complement entry to
   vanish.  The converse graph-to-rank half is checked as
   `rank_fromBlocks_zero₂₂_le_card_left` and
   `rank_fromBlocks_le_of_schur_complement_eq_zero`: Schur-complement zero
   forces rank at most the principal-block size via mathlib's LDU
   factorization and elementary row-span rank control of `fromBlocks A 0 0 0`.
   The arbitrary-coordinate packaging is checked as
   `toBlocks₂₁_eq_transpose_toBlocks₁₂_of_symm`,
	   `schur_complement_entry_eq_zero_of_rank_le_reindex`, and
	   `rank_le_of_reindexed_schur_complement_eq_zero`, transporting the canonical
	   Schur equivalence through `Matrix.reindex` for any equivalence
	   `ι ≃ r ⊕ q`.  The principal-patch graph characterization is now checked in
	   `BHWPermutation/SourceComplexSchurPatch.lean` as
	   `rank_eq_card_iff_reindexed_schur_complement_eq_zero`,
	   `sourceSymmetricRankExactStratum_iff_reindexed_schur_complement_eq_zero`,
	   and `sourceComplexGramVariety_iff_reindexed_schur_complement_eq_zero`:
	   on an invertible selected principal block of size `d + 1`, membership in
	   the source complex Gram variety is exactly symmetry plus vanishing
	   Schur complement.  This is the local graph model needed for the
	   Hall-Wightman regular-rank stratum, not a wrapper around the identity
	   theorem.  The rectangular all-minor implementation cover is also checked
	   in the same file: `reindexedRectSchurComplement`,
	   `rank_fromBlocks_zero₂₂_le_card_left_rect`,
	   `schur_complement_entry_eq_zero_of_rank_le_rect`,
	   `rank_fromBlocks_le_of_schur_complement_eq_zero_rect`,
	   `rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero`,
	   `sourceSymmetricRankExactStratum_iff_reindexed_rect_schur_complement_eq_zero`,
	   and `sourceComplexGramVariety_iff_reindexed_rect_schur_complement_eq_zero`.
	   This lets the regular-stratum cover use the already checked arbitrary
	   nonzero-minor extraction, while the principal-patch theorem remains the
	   Hall-Wightman-facing specialization.  The selected-minor complement
	   packaging is also checked as `selectedIndexComplement`,
	   `selectedIndexSumEquiv`, `selectedIndexSumEquiv_apply_selected`,
	   `selectedIndexSumEquiv_toBlocks₁₁`,
	   `isUnit_selectedIndexSumEquiv_toBlocks₁₁_det`, and
	   `sourceComplexGramVariety_iff_selected_rect_schur_complement_eq_zero`.
	   Thus an actual nonzero minor `sourceMatrixMinor n (d+1) I J Z ≠ 0`
	   directly produces the rectangular Schur chart of the source Gram variety.
	   The cover extraction is now checked as
	   `sourceMatrixMinor_ne_zero_left_injective`,
	   `sourceMatrixMinor_ne_zero_right_injective`,
	   `exists_sourceMatrixMinor_ne_zero_of_sourceSymmetricRankExactStratum`,
	   `exists_selected_rect_schur_chart_of_sourceSymmetricRankExactStratum`,
	   and
	   `exists_selected_rect_schur_chart_of_sourceComplexGramVariety_rankExact`:
	   every rank-exact point yields injective selected row/column maps, a
	   nonzero selected minor, and the selected Schur graph equivalence for the
	   source complex Gram variety on the resulting patch.  The corresponding
	   topology is checked as `isOpen_sourceMatrixMinor_ne_zero`,
	   `sourceMatrixMinor_ne_zero_relOpenInSourceComplexGramVariety`, and
	   `sourceComplexGramVariety_regularSelectedMinorPatch_relOpen`: selected
	   determinant-nonzero patches, and their intersections with the regular
	   rank-`d+1` stratum, are relatively open in the source complex Gram
	   variety.  The selected-chart dimension count is checked in the new small
	   companion `BHWPermutation/SourceComplexDimension.lean` as
	   `finrank_sourceSelectedComplexSymCoordSubspace`: the selected complex
	   symmetric-coordinate subspace has finrank
	   `n*m - m*(m-1)/2`, using the existing real dimension theorem and the
	   checked real/complex coordinate-key equivalences.  The same companion
	   now carries the lower-rank codimension arithmetic:
	   `sourceRankExactChartDim_sub_previous` proves the paper formula
	   `dim(rankExact D) - dim(rankExact (D-1)) = n-D+1`, and
	   `finrank_sourceSelectedComplexSymCoordSubspace_lowerRankCodim_ge_two`
	   gives codimension at least two in the singular case `D < n`.  The
	   complex source-density packet is now checked too in
	   `BHWPermutation/SourceComplexDensity.lean`: it complexifies
	   `sourceFullSpanTemplate`, uses the determinant polynomial of the
	   canonical regular minor along
	   `z + t • sourceComplexFullSpanTemplate d n`, and proves
	   `dense_sourceComplexGramRegularAt`.  The next implementation target in
	   that companion is now Lean-ready: under the necessary hard-range
	   hypothesis `d + 1 <= n`, a nonzero complex regular source minor makes the
	   selected Gram rows linearly independent; row-rank comparison gives
	   `d + 1 <= rank(sourceMinkowskiGram d n z)`, and the checked
	   `sourceComplexGramVariety_eq_rank_le` upper bound upgrades every regular
	   source Gram matrix to membership in
	   `sourceSymmetricRankExactStratum n (d + 1)`.  The immediate density
	   corollary is also Lean-ready: for any point of the source complex Gram
	   variety and any ambient open neighborhood, choose a source realization,
	   pull the neighborhood back along the continuous Gram map, use
	   `dense_sourceComplexGramRegularAt`, and push the chosen regular source
	   point forward with the rank-exact bridge.  Closedness of
	   `sourceComplexGramVariety d n` and
	   `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety` then
	   give
	   `closure (sourceSymmetricRankExactStratum n (d + 1)) =
	    sourceComplexGramVariety d n`.  The consumer corollary is now pinned:
	   every nonempty relatively open subset of `sourceComplexGramVariety d n`
	   meets `sourceSymmetricRankExactStratum n (d + 1)`, obtained by applying
	   `mem_closure_iff` to the ambient-open representative of the relatively
	   open set.  The checked consumer upgrades this to relative
	   density inside each relatively open source-variety domain `U`, and then
	   proves the pure continuity-extension lemma: if a continuous scalar-product
	   representative on `U` vanishes on
	   `U ∩ sourceSymmetricRankExactStratum n (d + 1)`, it vanishes on all of
	   `U`.  The production `SourceVarietyGermHolomorphicOn` hypothesis exposes
	   `ContinuousOn` through the checked
	   `SourceVarietyGermHolomorphicOn.continuousOn` plus the relative-open
	   subset helper, so the continuity-extension lemma applies directly to
	   theorem-2 representatives.
	   The easy-arity algebraic reduction is now pinned next: when
	   `n <= d + 1`, `sourceComplexGramVariety d n` equals
	   `sourceSymmetricMatrixSpace n`, since the rank bound in
	   `sourceComplexGramVariety_eq_rank_le` is automatic.
	   The full symmetric affine coordinate model for this easy branch is now
	   checked too: `sourceFullSymCoordMapCLM`,
	   `sourceFullSymCoordMap_mem_sourceSymmetricMatrixSpace`,
	   `continuous_sourceFullSymCoordMap`,
	   `differentiable_sourceFullSymCoordMap`,
	   `sourceSymmetricMatrixSpace_eq_range_sourceFullSymCoordMap`, and
	   `isOpen_sourceFullSymCoordMap_preimage_of_relOpen_of_le` identify the
	   symmetric affine space with selected symmetric coordinates and turn
	   relatively open easy-branch source-variety domains into honest open
	   finite-dimensional complex coordinate domains.  The connectedness
	   transport is now checked as
	   `isConnected_sourceFullSymCoordMap_preimage_of_relOpen_of_le`, using the
	   inverse coordinate map on the subtype `U`.  The easy-branch identity
	   theorem itself is now checked as
	   `sourceComplexGramVariety_identity_principle_easy`: it applies the
	   ordinary SCV identity theorem to `H ∘ sourceFullSymCoordMap n` on the
	   open connected coordinate domain and pushes equality back to `U`.  The
	   final global theorem is now checked as the intended short arity split:
	   use this checked easy theorem when `n <= d + 1`; when `d + 1 < n`, use
	   the checked regular-rank-stratum identity theorem and then invoke the
	   already checked rank-exact density/continuity extension.
	   The theorem-2 blueprint separates the strict branch into two genuine
	   packets: the local identity propagation packet, using the checked BHW
	   selected complex Gram chart / local image infrastructure rather than a new
	   Schur-wrapper layer, and the connected-regular-locus theorem for connected
	   relatively open subsets of the irreducible normal symmetric rank-bounded
	   variety.  Both are now checked.  This is the Hall-Wightman
	   irreducibility/normality content; it is not a corollary of density alone.
	   A principal-minor Schur cover is mathematically valid over `ℂ` and is the
	   route now used for the singular local-basis branch, via the checked
	   nonzero-principal-minor cover theorem.  The first algebraic bridge on this route is
	   now checked in `BHWPermutation/SourceComplexDensity.lean`:
	   `sourceMinkowskiGram_rank_le_sourceComplexConfigurationSpan_finrank` and
	   `sourceSymmetricRankExactStratum_exists_complexRegular_realization`.
	   The local complex-regular image packet is also checked there as
	   `sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`,
	   giving the connected source ball and relatively open rank-exact image
	   needed for the local identity-propagation theorem.  On the corrected
	   route the pullback helper is
	   `SourceVarietyGermHolomorphicOn.comp_sourceMinkowskiGram`; it uses a
	   germ local representative on the source-variety slice.  The local
	   propagation theorem
	   `sourceComplexGramVariety_rankExact_local_identity_near_point` is now
	   checked as well.  The conditional global propagation theorem
	   `sourceComplexGramVariety_rankExact_identity_principle_of_connected` is
	   now checked too: from connectedness of
	   `U ∩ sourceSymmetricRankExactStratum n (d + 1)`, it proves the full
	   rank-exact identity principle by a nonempty clopen zero-patch argument;
	   `sourceComplexGramVariety_identity_principle_of_connected_rankExact` then
	   extends the result to all of `U` via the checked dense-rank-exact
	   continuity theorem.  The strict source-side blocker was the global
	   connected regular-locus theorem; it is now checked, as are local
	   Schur/chart propagation, identity-principle assembly, and dense-extension
	   assembly.  The theorem-2 blueprint refines this global theorem into a
	   checked strict connectedness packet: the pure topological assembly
	   lemma
	   `sourceComplexGramVariety_rankExact_inter_relOpen_isConnected_of_local_basis`
	   is now checked.  The packet it reduced to has now also been closed: the
	   source-specific local connected rank-exact basis theorem, the connected
	   regular local-image strengthening, and the connected cone lemmas
	   are all checked.  The principal minor support lemma for symmetric matrices is
	   now checked in `BHWPermutation/SourceComplexSchurPatch.lean`; it uses
	   the checked complex symmetric rank factorization to turn a full-rank row
	   minor of `A` in `Z = A Aᵀ` into a nonzero principal minor of `Z`.
	   The Schur-complement rank-additivity theorem for singular
	   principal blocks is now checked in
	   `BHWPermutation/SourceComplexSchurPatch.lean`, together with direct
	   source-rank `≤` and exact-rank Schur consequences.  The hard mathematical
	   proof was the source local-basis theorem, i.e. Hall-Wightman's local
	   irreducibility/normality of the symmetric scalar-product determinantal
	   variety.  Two checked local-basis surfaces are now distinguished:
	   `sourceComplexGramVariety_local_rankExact_connected_basis` supplies the
	   connected rank-exact regular-locus input used by the identity-principle
	   layer, while `sourceComplexGramVariety_local_connectedRelOpen_basis`
	   supplies the actual connected rank-bounded source-variety tube.  The
	   lower-rank tube is checked by genuine Schur product charts plus the
	   connected rank-`<=` cone lemma, with no zero-Schur wrapper hiding the
	   lower-rank singular case.  The cone lemmas are proved through real
	   finite-dimensional content: nonzero scalar rank invariance, cone
	   invariance of `sourceSymmetricRankExactStratum` and
	   `sourceSymmetricRankLEVariety`, dot-Gram scaling,
	   path-connectedness of the full-rank complex source-configuration
	   Stiefel space using `MatrixLieGroup.GL_isPathConnected`, and the
	   small-ball radial contraction arguments.  The implementation should not
	   cite "rank-exact cone connectedness" as an opaque geometric black box for
	   rank-bounded topology.
	   The first cone support file is now checked as
	   `BHWPermutation/SourceComplexCone.lean`: it proves scalar rank
	   invariance, exact-stratum cone invariance, dot-Gram scaling, the
	   full-rank configuration predicate, the selected/standard coordinate
	   frames and their full-rank membership, left/right determinant-unit action
	   invariance for full-rank configurations, the corresponding left/right
	   `GL` path-joining lemmas, existence of a nonzero selected row minor for
	   every full-rank configuration, the selected-minor contraction to the
	   coordinate frame, the selected-frame-to-standard-frame path, full
	   Stiefel-space path-connectedness, continuity of the dot-Gram map, the
	   map from full-rank configurations to the exact stratum, the
	   exact-stratum full-rank dot-Gram representative theorem, the image
	   equality for the exact stratum, and path-connectedness of the exact
	   symmetric rank stratum.  It now also checks the radial endpoint paths
	   inside centered balls, the compact norm bound for an arbitrary path, the
	   scaled middle path, the path-connectedness of
	   `Metric.ball 0 ε ∩ sourceSymmetricRankExactStratum m r` for every
	   `r ≤ m`, and the final neighborhood form
	   `sourceSymmetricRankExactCone_small_connected`.  It also now checks
	   scalar rank non-increase, rank-`<=` cone invariance, path-connectedness of
	   `Metric.ball 0 ε ∩ sourceSymmetricRankLEVariety m r`, and
	   `sourceSymmetricRankLECone_small_connected`.  The cone blocker is
	   therefore closed.  The blueprint now spells out the next singular
	   Schur-product implementation packet.  Its first production layer is now
	   checked in `BHWPermutation/SourceComplexSchurGraph.lean`: the principal
	   Schur graph `sourcePrincipalSchurGraph`, its block-recovery and
	   Schur-complement recovery lemmas, symmetry of the graph, and the
	   rank-`≤`/rank-exact graph equivalences using the checked principal Schur
	   rank theorem.  The cone theorem has also been transported to arbitrary
	   finite complement index types in
	   `BHWPermutation/SourceComplexConeTransport.lean`, so the Schur complement
	   coordinate no longer has a `Fin`-only type mismatch.  The singular
	   local-basis work is now checked: it constructs the product neighborhood
	   around a lower-rank point and proves the final continuous-image
	   connectedness argument feeding
	   `sourceComplexGramVariety_local_rankExact_connected_basis`.  This is
	   genuine Hall-Wightman finite-dimensional geometry, not a wrapper around
	   the local-basis theorem.  The determinant-unit inverse-continuity lemma
	   `continuousOn_matrix_inv_of_isUnit_det` is now checked in
	   `SourceComplexSchurGraph.lean`; the graph-continuity theorem
	   `continuousOn_sourcePrincipalSchurGraph` is now checked there as well,
	   with a coordinatewise proof expanding only the finite lower-right
	   Schur term.  The product-neighborhood extraction theorem
	   `exists_sourcePrincipalSchurGraph_product_subset_open` is now checked:
	   from an open ambient neighborhood `N0` of the graph point it returns open
	   `A`, `B`, and `S` neighborhoods whose whole graph image lies in `N0`, with
	   the `A` neighborhood contained in the determinant-unit locus.  The
	   graph-image connectedness theorems
	   `isConnected_sourcePrincipalSchurGraph_rankExact_image` and
	   `isConnected_sourcePrincipalSchurGraph_rankLE_image`, together with the
	   rank-exact/rank-`<=` image-subset theorems
	   `sourcePrincipalSchurGraph_rankExact_image_subset` and
	   `sourcePrincipalSchurGraph_rankLE_image_subset`, are now checked too.
	   The `A`-factor local topology is now checked through
	   `isOpen_matrix_det_isUnit`, `exists_pos_ball_subset_isUnit_det`, and
	   `isConnected_symmetric_matrix_ball`; these use the concrete Frobenius
	   matrix norm scope for finite-dimensional matrix balls.  The rectangular
	   `B`-factor ball connectedness is now checked as `isConnected_matrix_ball`.
	   The Schur-coordinate continuity needed for relative openness is now
	   checked too:
	   `continuousOn_principalBlock_invEntry` and
	   `continuousOn_reindexedPrincipalSchurComplement`.
	   The finite matrix lemma `matrix_eq_zero_of_rank_eq_zero` is checked, so
	   the singular basepoint Schur complement can be converted from rank zero
	   to the zero matrix after Schur rank additivity.
	   The Schur chart inverse-coordinate equality
	   `sourcePrincipalSchurGraph_coordinates_eq_of_symmetric` is now checked:
	   a symmetric matrix on a determinant-unit principal patch is exactly the
	   graph of its principal block, rectangular block, and Schur-complement
	   coordinate.  This supplies the forward inclusion needed for the final
	   equality between `V ∩ rankExact` and the Schur graph image.
	   The coordinate symmetry lemmas
	   `principalBlock_transpose_eq_of_symmetric` and
	   `reindexedRectSchurComplement_transpose_eq_of_symmetric` are also checked,
	   so a symmetric source matrix lands in the symmetric `A` and `S` factors of
	   the singular product chart.
	   The ambient Schur-coordinate openness theorem
	   `isOpen_sourcePrincipalSchurCoordinatePatch` is now checked too: open
	   conditions on `N0`, the principal block, rectangular block, and
	   Schur-complement coordinate cut out an open determinant-unit patch in the
	   ambient matrix space.  The final relative-open chart is therefore exactly
	   this patch intersected with `sourceComplexGramVariety d n`.
	   The exact graph-image equality
	   `sourcePrincipalSchurGraph_rankExact_image_eq_coordinatePatch` is now
	   checked: once the parameter product has been shrunk so its graph lies in
	   the requested ambient neighborhood `N0`, the rank-exact part of the Schur
	   coordinate patch is precisely the graph image of
	   `Aset × Bset × (Sset ∩ rankExact)`.
	   The open-coordinate variant
	   `sourcePrincipalSchurGraph_rankExact_image_eq_openCoordinatePatch` is now
	   checked as well, so the final local-basis proof can use the open `A`
	   neighborhood for relative openness and the symmetric `A` factor for
	   connectedness without redoing set algebra.
	   The rank-bounded analogues
	   `sourcePrincipalSchurGraph_rankLE_image_eq_coordinatePatch` and
	   `sourcePrincipalSchurGraph_rankLE_image_eq_openCoordinatePatch` are also
	   checked, so the lower-rank connected source-variety tube is identified
	   with the continuous image of the connected rank-`<=` Schur product.
	   The singular topology target is now checked as
	   `sourceComplexGramVariety_local_rankExact_connected_basis_singular`: it
	   constructs the actual `Aset`, `Bset`, and `Sset` around a lower-rank
	   point and proves the final radius-shrinking and assembly for the singular
	   rank-exact local-basis theorem.  The rank-bounded singular tube is now
	   separately checked as
	   `sourceComplexGramVariety_local_connectedRelOpen_basis_singular`; the
	   strict and all-arity connected local-basis theorems are checked as
	   `sourceComplexGramVariety_local_connectedRelOpen_basis_strict` and
	   `sourceComplexGramVariety_local_connectedRelOpen_basis`.  The easy-arity
	   branch uses connected balls in the full symmetric affine space, while the
	   strict lower-rank branch uses the rank-`<=` Schur tube.  The regular rank
	   The compact-path source tube is now checked by a connected-component
	   argument.  For a relatively open source-variety domain `D` and a point
	   `Z0 ∈ D`, the component `connectedComponentIn D Z0` is relatively open:
	   around each point of the component, the checked local connected basis
	   supplies a connected relatively open neighborhood inside `D`, and
	   `IsPreconnected.subset_connectedComponentIn` plus
	   `connectedComponentIn_eq` places that neighborhood back inside the same
	   component; the component is the union of these local neighborhoods.  The
	   corresponding checked theorem chooses
	   `Wtube = connectedComponentIn D (γ 0)`.  Connectedness and containment are
	   the standard `connectedComponentIn` facts, the starting connected set
	   `W0` lies in the component by
	   `hW0_conn.isPreconnected.subset_connectedComponentIn`, and the path lies
	   in the same component because `Set.range γ` is preconnected.  Thus no
	   finite-subdivision or hidden path-chain lemma remains in this step.
	   The checked declarations are
	   `IsRelOpenInSourceComplexGramVariety.iUnion`,
	   `sourceComplexGramVariety_connectedComponentIn_relOpen`, and
	   `sourceComplexGramVariety_connectedRelOpenTube_around_compactPath`.
	   The regular rank
	   branch of the rank-exact local-basis
	   theorem has also been tightened:
	   `sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`
	   now returns `IsConnected O` for the produced relatively open
	   rank-exact image, proved by showing that `O` is exactly the continuous
	   source-Gram image of the connected source ball.  The regular branch is
	   now checked as
	   `sourceComplexGramVariety_local_rankExact_connected_basis_regular`.
	   The full local-basis theorem is now checked as
	   `sourceComplexGramVariety_local_rankExact_connected_basis`, splitting
	   between the checked regular branch and checked singular Schur product-chart
	   branch.  This closes
	   `sourceComplexGramVariety_rankExact_inter_relOpen_isConnected`,
	   `sourceComplexGramVariety_rankExact_identity_principle`, and the final
	   legacy strong-API `sourceComplexGramVariety_identity_principle` in
	   `BHWPermutation/SourceComplexDensity.lean`; the corrected route now
	   exposes the germ analogue under the same name,
	   `sourceComplexGramVariety_identity_principle`, using the same
	   rank-exact/continuity proof and
	   `SourceVarietyGermHolomorphicOn.continuousOn` at the dense-extension
	   step.
	   The pairwise
	   `sourceDistributionalUniquenessSetOnVariety_of_realEnvironment` proof is
	   now checked in `BHWPermutation/SourceDistributionalUniqueness.lean` as the
	   direct `H := Φ - Ψ` consumer, not a wrapper ladder.  Deep Research audit
   `v1_ChdsVFR2YVpiQUN0U1lfdU1Qa1pidjZBMBIXbFRUdmFaYkFDdFNZX3VNUGtaYnY2QTA`
   agrees with the rank-bounded-variety and irreducible-analytic-identity
   theorem shape, and flags the same hidden obligations: strong/local-ambient
   holomorphy, singular lower-rank handling, and analytic irreducibility of the
   source symmetric determinantal variety.  The blueprint now also records the
   needed complex symmetric rank factorization and warns that the source-space
   pullback shortcut is insufficient unless it proves the same irreducibility /
   monodromy content.  The local chart target is relative openness in
   the scalar-product variety; it is not the false affine claim that the Gram
   image contains an open subset of `G0 + range dG_x0`.  The algebraic
   selected-coordinate uniqueness step
   `sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero`
   and its chart consequence
   `sourceRealGramMap_constant_on_selectedVerticalFibers` are now checked.
   This replaces the earlier vertical-path/integration idea: on one fixed
   nonzero selected-minor chart, selected Gram coordinates determine the full
   Gram matrix, hence the selected implicit chart has full-Gram-constant
   vertical fibers after shrinking to the same minor chart.
   The next relative-open image step is now documented with the extra
   algebraic bridge that the chart proof genuinely needs:
   `sourceSelectedGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop`,
   `sourceSelectedRows_span_top_of_selectedGramCoord_eq_regular`, and
   `sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero_of_mem_variety`.
   These avoid the hidden false assumption that an arbitrary realization of a
   nearby Gram matrix in `sourceRealGramVariety d n` already lies in the same
   source minor chart; selected coordinates of one regular chart point must
   determine the whole Gram matrix for any realization in the variety.  This
   bridge, the open-neighborhood relative image theorem
   `sourceRealGramMap_localRelOpenImage_in_open_of_regular`, and its
   `V = Set.univ` corollary
   `sourceRealGramMap_localRelOpenImage_of_regular` are now checked in
   `BHWPermutation/SourceRegularRank.lean`.
   The OS-side constructor is now pinned to a field-by-field Lean transcript:
   the strengthened `BHW.os45_adjacent_singleChart_commonBoundaryValue` must
   export one and the same OS45 patch `V` with Jost membership, both adjacent
   extended-tube memberships, and an
   `BHW.AdjacentOSEOWDifferenceEnvelope`.  The theorem-2 blueprint now separates
   the OS45 instantiation theorem
   `BHW.os45_adjacent_commonBoundaryEnvelope` from the direct-coordinate
   packaging: it constructs the common chart, instantiates the checked
   one-chart theorem `SCV.chartDistributionalEOW_local_envelope` at an ordered
   identity-sector horizontal edge, glues the local seed to the OS45 side
   components, and exports a holomorphic branch-difference function with the
   Wick/real trace identities.  The older global
   `SCV.local_distributional_edge_of_the_wedge_envelope` surface is retained as
   a future SCV packaging target, not as the active Slot 1 input.  The
   finite-order primitive shortcut is rejected because the
   multi-variable integration constants are infinite-dimensional, and the
   final patching route has been sharpened further: derive `0 < m` from
   `C.Nonempty` and `0 ∉ C`, choose one global cone basis in `C`, use a
   fixed-basis local chart-window theorem at every edge point, transport each
   coordinate envelope back through the complex affine chart equivalence, and
   patch only after the fixed positive coordinate cone supplies common
   identity-theorem seeds on overlaps.  This rules out the per-point-basis
   shortcut that would leave overlap compatibility unjustified.  The false
   polynomial-correction shortcut is not used.  The checked
   real-mollification infrastructure in `SCV/LocalDistributionalEOW.lean`
   now supplies the checked regularized common-boundary extraction
   `SCV.localRealMollify_commonContinuousBoundary_of_clm`.  The nonzero-envelope
   recovery layer is also checked through the exact QFT-free substrate:
   `SCV.complexTranslateSchwartz`, `SCV.schwartzTensorProduct₂`,
   `SCV.realConvolutionTest`,
   `SCV.translationCovariantProductKernel_descends`,
   `SCV.distributionalHolomorphic_regular`,
   `SCV.regularizedEnvelope_productKernel_dbar_eq_zero`,
   `SCV.translationCovariantKernel_distributionalHolomorphic`,
   `SCV.regularizedEnvelope_holomorphicDistribution_from_productKernel`,
   `SCV.regularizedEnvelope_pointwiseRepresentation_of_productKernel`,
   `SCV.regularizedEnvelope_deltaLimit_agreesOnWedges`, and
   `SCV.regularizedEnvelope_chartEnvelope_from_productKernel`.  The remaining
   theorem-2 SCV work is upstream of that checked consumer: extract the local
   continuous EOW theorem and construct the regularized local EOW
   product-kernel family with the exact `K,G,hcov,hG_holo,hK_rep` fields.  The
   checked downstream consumer uses `bvt_F_acrOne_package` to prove vanishing.
   The first SCV substrate slice is now checked in
   `SCV/DistributionalEOWKernel.lean`: `complexTranslateSchwartz`,
   `schwartzTensorProduct₂`, `realConvolutionShearCLE`,
   `complexRealFiberIntegralRaw`, `integrable_complexRealFiber`,
   `baseFDerivSchwartz`,
   `exists_norm_pow_mul_complexRealFiberIntegralRaw_le`,
   `exists_integrable_bound_baseFDerivSchwartz`,
   `hasFDerivAt_complexRealFiberIntegralRaw`, the raw integral smoothness and
   decay theorems, `complexRealFiberIntegral`, and
   `realConvolutionTest` with the exact OS-II sign and its translation identity
   `realConvolutionTest φ ψ z = ∫ t, φ (z - realEmbed t) * ψ t`.
   The identity
   `realConvolutionTest (complexTranslateSchwartz a φ) ψ =
    realConvolutionTest φ (translateSchwartz a ψ)`
   is the checked sign bridge into product-kernel descent.
   The same SCV file now checks the first fiber-descent primitives
   `complexRealFiberTranslateSchwartzCLM`,
   `complexRealFiberIntegral_fiberTranslate`,
   `complexRealFiberIntegral_schwartzTensorProduct₂`,
   `translateSchwartz_translateSchwartz`,
   `complexTranslateSchwartz_complexTranslateSchwartz`,
   `shearedProductKernelFunctional`, and
   `IsComplexRealFiberTranslationInvariant`, plus
   `complexRealFiberTranslate_shearedTensor_eq`.  The same SCV substrate now
   checks the pure coordinate transport needed for the mixed fiber
   factorization: `headBlockShift`, `realBlockFlattenCLE`,
   `complexToFinTwoCLE`, `complexChartRealFlattenCLE`, `finAppendCLE`,
   `mixedChartFiberFirstCLE`, its head/tail real-imaginary apply lemmas,
   `mixedChartFiberFirstCLE_symm_headBlockShift`, and the sign-sensitive
   transport identity `mixedChartFiberFirstCLE_translate`.  The transported
   fiber-integral identity
   `complexRealFiberIntegral_eq_transport_integrateHeadBlock`, the pure-SCV
   head-block factorization theorem, and the mixed
   `map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant`
   theorem are now checked.  The normalized-cutoff consumer is also checked in
   `SCV/DistributionalEOWKernelFactorization.lean`:
   `SCV.schwartzTensorProduct₂CLMRight`,
   `SCV.complexRealFiberTranslationDescentCLM`, and
   `SCV.map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant`.
   The next proof-doc/Lean target is therefore the product-kernel extension and
   translation-covariant descent layer:
   `SCV.schwartzKernel₂_extension`,
   `SCV.translationCovariantProductKernel_descends`, and
   `SCV.distributionalHolomorphic_regular`.  The descent theorem is now
   documented with the correct global/local split:
   first prove the global pure-SCV theorem from
   `SCV.ProductKernelRealTranslationCovariantGlobal`, then derive the
   support-restricted envelope corollary from
   `SCV.ProductKernelRealTranslationCovariantLocal` after applying the fixed
   cutoff.  The remaining gap before the sheared product-kernel descent is the
   mixed product-tensor density/kernel-extension theorem: product covariance is
   currently an equality on `schwartzTensorProduct₂` tests, and promotion to all
   mixed Schwartz tests must go through `schwartzKernel₂_extension` or an
   equivalent uniqueness principle.  Before that density promotion, the next
   100%-ready Lean slice is the tensor-level sign theorem
   `SCV.shearedProductKernel_fiberTranslate_shearedTensor_eq_self_of_productCovariant`:
   combine `SCV.complexRealFiberTranslate_shearedTensor_eq` with global product
   covariance at `-a` and
   `SCV.translateSchwartz_translateSchwartz` to prove that the sheared
   functional is invariant on every sheared product tensor.  This closes the
   exact OS-II sign/covariance calculation on the generator family without
   pretending that product-tensor density has already been proved.  The next
   100%-ready promotion theorem is conditional on the precise dense-span
   blocker `SCV.ShearedProductTensorDense m`: define
   `SCV.shearedProductTensorSet` as the sheared `schwartzTensorProduct₂`
   generator family, take its complex linear span, prove equality of the two
   continuous functionals on that span by `Submodule.span_induction`, and use
   the closed-equalizer dense-set argument to obtain
   `SCV.shearedProductKernel_fiberInvariant_of_productCovariant_of_shearedProductTensorDense`.
   Combining that with the checked normalized fiber factorization gives
   `SCV.translationCovariantProductKernel_descends_of_shearedProductTensorDense`.
   This is a genuine reduction: all remaining unproved mathematical content is
   isolated in `SCV.ShearedProductTensorDense m`, equivalent to the mixed
   two-space product-density/kernel-extension theorem.  The conditional
   promotion/descent package is now checked in
   `SCV/DistributionalEOWProductKernel.lean`; the next proof-doc task is to
   make `SCV.ShearedProductTensorDense m`/`SCV.schwartzKernel₂_extension`
   itself Lean-ready without importing the Wightman `schwartz_nuclear_extension`
   axiom.
   The first Lean-ready part of that density task is now checked: define the
   unsheared simple-product generator family
   `SCV.productTensorSet m`, its span `SCV.productTensorSpan m`, and the
   standard blocker `SCV.ProductTensorDense m`.  Then prove
   `SCV.shearedProductTensorDense_of_productTensorDense` by transporting
   density through
   `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
     (SCV.realConvolutionShearCLE m)`.  The checked proof should use
   `SCV.shearedProductTensorSet_eq_image_productTensorSet`,
   `Submodule.map_span`,
   `Submodule.dense_iff_topologicalClosure_eq_top`, surjectivity from
   `SCV.compCLMOfContinuousLinearEquiv_symm_left_inv`, and
   `DenseRange.topologicalClosure_map_submodule`.  The consumer corollary
   `SCV.translationCovariantProductKernel_descends_of_productTensorDense`
   simply feeds this transported density into the already checked
   sheared-density descent theorem.  This is not a wrapper inflation: it
   replaces the shear-specific blocker by the standard unsheared product
   Schwartz density theorem, which is exactly the remaining functional-analytic
   content of `SCV.schwartzKernel₂_extension`.
   The next density proof is now pinned to a pure-SCV/GaussianField route, not
   to Wightman `schwartz_nuclear_extension`.  Add
   `SCV/ComplexSchwartz.lean` with `SCV.schwartzRealPartCLM`,
   `SCV.schwartzImagPartCLM`, `SCV.schwartzOfRealCLM`, and
   `SCV.complexSchwartzDecomposeCLE`, importing no Wightman files.  These
   SCV-owned names deliberately avoid colliding with the already existing
   Wightman `SchwartzMap.*` decomposition declarations.  Add
   `SCV/SchwartzExternalProduct.lean` for the checked external product
   `(x,y) ↦ φ x * ψ y`, and `SCV/ProductDensity.lean` for
   `SCV.twoBlockProductSchwartz`, `SCV.flatMixedCLM`,
   `SCV.flattenMixedFunctional`, and the bridge
   `SCV.flatTwoBlockProduct_eq_mixedProduct`.  The next theorem in that
   product-density companion proves, for `0 < m`, that any mixed-chart
   complex continuous linear functional vanishing on all
   `SCV.schwartzTensorProduct₂ φ ψ` is zero.  The proof transports the
   functional through `SCV.mixedChartFiberFirstCLE m`, uses
   `GaussianField.productHermite_schwartz_dense (D := ℝ) (m + m*2)` on the
   flat domain `Fin (m + m*2) -> ℝ`, splits each one-dimensional Hermite
   product into the first `m` real-fiber coordinates and the last `m*2`
   flattened complex-chart coordinates, and then reconstructs complex-valued
   tests from real/imaginary parts with `SCV.complexSchwartzDecomposeCLE`.
   This product-density companion is now checked through the final density
   theorem: `SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts`,
   `SCV.mixedProductCLM_zero_of_zero_on_productTensor`,
   `SCV.ProductTensorDense_of_pos`, `SCV.ProductTensorDense_zero`, and
   `SCV.ProductTensorDense_all`.  The final `SCV.ProductTensorDense_of_pos`
   is the same Hahn-Banach
   separation argument as `Wightman/Reconstruction/DenseCLM.lean`, with the
   new pure-SCV CLM-uniqueness theorem replacing Wightman nuclear uniqueness.
   The `m = 0` case must be a direct singleton-domain proof using the constant
   product tensor; it is not covered by GaussianField's positive-dimensional
   product-Hermite theorem.  The resulting implementation targets are:

   ```lean
   theorem SCV.flatTwoBlockProduct_eq_mixedProduct
   theorem SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts
   theorem SCV.mixedProductCLM_zero_of_zero_on_productTensor
   theorem SCV.ProductTensorDense_of_pos
   theorem SCV.ProductTensorDense_zero
   theorem SCV.ProductTensorDense_all
   ```

   `SCV.ProductTensorDense_all` now feeds directly into the already checked
   `SCV.translationCovariantProductKernel_descends_of_productTensorDense` via
   the new `SCV.translationCovariantProductKernel_descends`, removing the
   product-kernel density blocker from theorem 2.
   The local distributional-EOW support-preservation layer is now checked in
   `SCV/DistributionalEOWSupport.lean`, not introduced as a new theorem
   wrapper.  It proves `SCV.KernelSupportWithin_hasCompactSupport`, because
   the production predicate is only closed-ball topological-support containment
   and compact support follows from finite-dimensional compactness of closed
   balls.  It also proves
   `SCV.directionalDerivSchwartzCLM_tsupport_subset`,
   `SCV.directionalDerivSchwartzCLM_supportsInOpen`,
   `SCV.dbarSchwartzCLM_tsupport_subset`, and `SCV.SupportsInOpen.dbar`.
   These are the exact lemmas consumed by the upcoming
   `regularizedEnvelope_productKernel_dbar_eq_zero` integration-by-parts
   package: they ensure every `dbarSchwartzCLM` test remains compactly
   supported inside the same open set `U0`.
   The next `∂bar` algebra slice is also fixed at theorem level:
   `SCV/DistributionalEOWDbar.lean` proves
   `SCV.integral_mul_directionalDerivSchwartzCLM_right_eq_neg_left`,
   `SCV.integral_mul_dbarSchwartzCLM_right_eq_neg_left`, and
   `SCV.integral_mul_dbarSchwartzCLM_right_eq_zero_of_dbar_eq_zero`.  The file
   now also proves
   `SCV.integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz`,
   the algebraic endpoint of the local cutoff argument.  Its hypotheses are
   exactly the data the cutoff must produce: a Schwartz representative `G`
   agreeing with the holomorphic factor on
   `tsupport (dbarSchwartzCLM j φ)` and satisfying
   `dbarSchwartzCLM j G = 0` on `tsupport φ`.
   The first cutoff subtheorem is now checked in
   `SCV/DistributionalEOWCutoff.lean`:
   `SCV.exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen`.  It uses
   nested thickenings of the compact set `K = tsupport φ ⊆ U`, applies
   `exists_contMDiff_support_eq_eq_one_iff` to
   `thickening r₂ K` and `closure (thickening r₁ K)`, and returns a smooth
   real cutoff equal to one on an open neighborhood of `K` with compact
   topological support inside `U`.
   The representative theorem is now checked in
   `SCV/DistributionalEOWRepresentative.lean`:
   `SCV.exists_local_schwartz_representative_eq_on_open` forms the
   zero-extended compactly supported smooth function `χ * F`, converts it into
   a Schwartz map, and proves agreement with `F` on the cutoff neighborhood.
   The pointwise Cauchy-Riemann theorem
   `SCV.dbarSchwartzCLM_eq_zero_on_of_eqOn_holomorphic` derives local
   coordinate `∂bar` vanishing from
   `hF_holo.analyticOnNhd_of_finiteDimensional hU_open`.  These feed
   `SCV.exists_local_dbarClosed_schwartz_representative`, and
   `SCV.integral_holomorphic_mul_dbarSchwartz_eq_zero` follows immediately by
   the checked localization lemma.  The product-kernel consumer
   `SCV.regularizedEnvelope_productKernel_dbar_eq_zero` is now checked too:
   it applies the product-kernel representation to
   `dbarSchwartzCLM j φ`, using `SupportsInOpen.dbar`, and then invokes
   `SCV.integral_holomorphic_mul_dbarSchwartz_eq_zero` for the scalar
   holomorphic kernel `G ψ`.  The continuity-passage theorem
   `SCV.translationCovariantKernel_distributionalHolomorphic` is now checked
   under the concrete approximate-identity hypotheses
   `∀ᶠ i, KernelSupportWithin (ψι i) r` and
   convergence of `realConvolutionTest θ (ψι i)` to `θ` in the Schwartz
   topology for every `θ`.  The next genuine theorem-2 SCV target is therefore
   the approximate-identity construction that supplies those two hypotheses:
   `SCV.exists_normalized_schwartz_bump_kernelSupportWithin`,
   `SCV.exists_shrinking_normalized_schwartz_bump_sequence`,
   `SCV.tendsto_realConvolutionTest_of_shrinking_normalized_support`, and
   `SCV.exists_realConvolutionTest_approxIdentity` are now checked.  The
   implemented proof uses the exact Lean slots recorded in
   `docs/scv_infrastructure_blueprint.md`: kernel `L¹` mass from real
   nonnegative normalization, `norm_realEmbed_le`, `continuous_realEmbed`,
   support-to-zero from `KernelSupportWithin`, the translated-derivative
   identity, integrability of the translated derivative kernel, zeroth-order
   and all-orders derivative-through-convolution identities, the global
   mean-value linear small-translation estimate in Schwartz seminorms, and the
   final `WithSeminorms` convergence argument.
   Because `SCV/DistributionalEOWKernel.lean` is now a checked, sorry-free
   1000-line support file, the next implementation stage uses new pure-SCV
   companions rather than growing it.  `SCV.HeadBlockIntegral` is now
   implemented directly as a finite-dimensional real fiber integral, adapting
   the checked `complexRealFiberIntegral` estimates to the base/fiber product
   `((Fin n -> ℝ) × (Fin m -> ℝ))`; the public theorem
   `SCV.integrateHeadBlock_apply_finAppend` is checked and reduces by the
   continuous-linear equivalence `headTailAppendCLE`.  The corresponding mixed
   chart transport theorem
   `SCV.complexRealFiberIntegral_eq_transport_integrateHeadBlock` is checked in
   `SCV/DistributionalEOWKernelTransport.lean`.  The existing Wightman
   `SliceIntegral.lean`, `BlockIntegral.lean`, and
   `HeadBlockTranslationInvariant.lean` files remain source patterns only and
   are not imported into SCV.  The next descent-side checked lemma is now also
   in `SCV.HeadBlockIntegral`: `integrateHeadBlock_translate_head`, proving
   that the quotient map is invariant under translating the integrated head
   coordinates.  The remaining head-block factorization proof is pinned to the
   recursive quotient descent in the checked Wightman source pattern: prove
   the one-coordinate quotient through `sliceIntegral` using the
   finite-dimensional `headFiberAntideriv`, then induct over the head block.
   The direct quotient algebra needed by that
   induction is now also checked in `SCV.HeadBlockIntegral`:
   `integrateHeadBlock_zero`, `integrateHeadBlock_add`, and
   `integrateHeadBlock_sub`.  `SCV/TranslationDifferentiation.lean` now checks
   the QFT-free translate difference-quotient theorem, and
   `SCV.HeadBlockIntegral` now checks
   `IsHeadBlockTranslationInvariantSchwartzCLM` and
   `map_lineDeriv_headBlockShift_eq_zero`, so invariant functionals are known
   to annihilate head-coordinate derivatives.  `SCV/SchwartzPrependField.lean`
   now checks the collision-free pure-SCV fixed-head product package
   `SCV.tailCLM`, `SCV.prependField`, and `SCV.prependFieldCLMRight`.
   `SCV/HeadFiberAntideriv.lean` now checks the first slice-integral batch:
   `tailInsertCLM`, `sliceIntegralRaw`, the Fubini theorem
   `integral_sliceIntegralRaw`, the slice decay majorants, differentiated
   slice formulas through `contDiff_sliceIntegralRaw`,
   `decay_sliceIntegralRaw`, `sliceIntegral`, `integrable_sliceSection`, the
   complex algebra/prepend identities including `sliceIntegral_prependField`,
   and the `iicZeroSlice` derivative/`ContDiff` package.
   `SCV/HeadFiberAntiderivInterval.lean` now checks `hasDerivAt_integral_Iic`,
   `intervalPiece`, the product differentiability split,
   `contDiff_intervalPiece`, `headFiberAntiderivRaw`,
   `headFiberAntiderivRaw_eq_interval_add_iic`, and
	   `lineDeriv_headFiberAntiderivRaw`.  `SCV/HeadFiberAntiderivDecay.lean`
	   now checks the remaining head-fiber work: zero-slice preservation under
	   pure-tail derivatives, the raw primitive derivative identities, the
	   `Set.Ioi` complementary-tail representation, zeroth-order and full
	   iterated-derivative decay, and final `headFiberAntideriv` Schwartz
	   packaging with pointwise and operator-form head-direction FTC.  No
	   Wightman import is used for these extractions.  The
	   one-coordinate descent layer in `SCV/HeadBlockDescent.lean` now checks:
	   head-translation invariant functionals kill head derivatives, vanish on
	   zero `sliceIntegral`, factor through `sliceIntegral` using a concrete
	   normalized bump, and compare any two tests with equal `sliceIntegral`.
	   The general head-block descent layer in `SCV/HeadBlockDescent.lean` also
	   now checks: the pure finite-dimensional reindexing API, the fixed-tail
	   head section, `integrateHeadBlock_sliceIntegral_reindex`, the reindexed
	   head-block translation identities, preservation of remaining-head
	   invariance under one-coordinate descent, and
	   `map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV`.
	   The mixed-chart consumer in
	   `SCV/DistributionalEOWKernelTransport.lean` now also checks
	   `map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant`,
	   transporting fiber-translation invariance through
	   `mixedChartFiberFirstCLE` and using
	   `complexRealFiberIntegral_eq_transport_integrateHeadBlock` plus the
	   checked head-block descent theorem.
	   The general proof uses a documented
	   SCV-specific bridge: because `SCV.integrateHeadBlock` is the direct
	   finite-dimensional integral rather than the old recursive definition,
	   it first proves `integrateHeadBlock_sliceIntegral_reindex` by the fixed-tail
	   `integral_sliceIntegralRaw`/Fubini argument recorded in
	   `docs/scv_infrastructure_blueprint.md`.  The blueprint now fixes the
	   exact Lean route for that bridge: extract a pure SCV
	   `schwartzPartialEval₂` package, define `fixedTailHeadSection` by
	   partial evaluation after `finAppendCLE`, prove the cast identity by the
	   three finite-index cases, and apply the already checked
	   `integral_sliceIntegralRaw`.  The recursive theorem transcript is also
	   pinned to the checked Lean route: the `m = 0` base case uses the
	   zero-dimensional volume/Dirac identity and
	   `Fin.append default (castFinCLE (Nat.zero_add n) x) = x`, and the
	   successor step uses the new direct/recursive bridge to convert equality
	   of full head-block integrals into equality of the sliced remaining
	   integrals before applying the induction hypothesis.
	   The
	   scratch algebra in
   `test/proofideas_head_block_helpers.lean` has been independently checked:
   it contains 19 proved helper theorems, not the 15 recorded in
   `agents_chat.md` #1313.  Port only the helpers consumed by the immediate
   proof transcript; do not turn the scratch inventory into a wrapper layer.
	   The proof-doc gap exposed by the source audit is now closed in
	   `docs/scv_infrastructure_blueprint.md`: the precursor extraction, the
	   first `HeadFiberAntideriv.lean` slice, and
	   `HeadFiberAntiderivInterval.lean` and `HeadFiberAntiderivDecay.lean` are
	   now checked.  The blueprint records the exact declaration order for the
	   decay file and the proof transcript that was implemented.  The next local
	   file should be `SCV/HeadBlockDescent.lean`, the recursive quotient-descent
	   port of the checked Wightman source pattern rather than a free-floating
	   wrapper layer.
   The #1307 audit has been folded into the route: `LocalTranslateMargin` is
   only the explicit closed-ball real-translation support condition, the final
   `SCV.local_distributional_edge_of_the_wedge_envelope` theorem must include
   uniqueness on the constructed open set, the
   `distributionalHolomorphic_regular` input is preceded by a concrete
   regularity package.  The later ordered-edge correction changes the immediate
   OS45 boundary-value step: Slot 1 now uses continuous horizontal-edge
   boundary values on a compact local edge window, so the compact-subcone
   strengthening of `bvt_boundary_values` is no longer the local seed blocker.
   Historical note: the next proof-doc frontier at this point was
   `SCV.distributionalHolomorphic_regular`.  That frontier is no longer the
   theorem-2 Slot 1 blocker after the later checked SCV recovery and one-chart
   EOW passes.  The active theorem-2 proof-doc frontier is now the
   identity-order OS45 instantiation of
   `SCV.chartDistributionalEOW_local_envelope`: choose an ordered perturbation,
   use the checked identity selector, reformulate the false horizontal-edge
   common-boundary shortcut, call the one-chart theorem only after the corrected
   boundary-value hypotheses are available, then glue to the finite Wick/real
   traces through side components.  The equal-time local-wedge audit remains as
   the reason the old post-radius plan is retired, not as the next theorem to
   prove.  The blueprint
   still records the Lean
   helper sequence: `dzSchwartzCLM` and its support lemmas, the checked
   coordinate-Laplacian identity
   `complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz`, the reduction from
   distributional `∂bar`-holomorphy to local harmonicity, the localized Weyl
   lemma/parametrix for the real Laplacian after transport from the plain
   chart to a Euclidean model, the checked `pointwiseDbar`, Euclidean
   chart/Schwartz transport bridges, coordinate-direction transport,
   Laplacian transport, transported distribution, and support transport,
   plus support transport in both directions, the volume-preserving
   chart-change theorem, and the Euclidean-representative pullback theorem.
   The first Euclidean moving-kernel layer for that Weyl route, including
   reflected support control, derivative commutation, first-order translation
   seminorm estimates, the pointwise quotient-derivative identity,
   compact-kernel continuity, Schwartz-topology difference-quotient
   convergence, and the one-parameter derivative theorem for reflected
   regularizations, is now checked in `SCV/EuclideanWeyl.lean`.  The next
   proof-doc/implementation frontier has advanced through the direction-uniform
   Fréchet remainder estimate, the scalar
   `hasFDerivAt_regularizedDistribution` theorem, and
   `contDiff_regularizedDistribution` in the new
   `SCV/EuclideanWeylFrechet.lean` companion file.  The checked ladder is
   recorded down to Lean pseudocode in `docs/scv_infrastructure_blueprint.md`:
   package `LineDeriv.bilinearLineDerivTwo ℝ φ` as
   `euclideanSecondLineDerivDirectionCLM`, expand the diagonal in the
   `EuclideanSpace.basisFun ι ℝ` basis, bound coordinates using
   `EuclideanSpace.norm_sq_eq` plus `Finset.single_le_sum`, apply a finite-sum
   seminorm triangle inequality to get
   `exists_seminorm_secondLineDeriv_unit_bound`, promote it to the translated
   second-derivative bound, obtain the uniform quotient and quadratic
   remainder estimates, and compose the resulting Schwartz-topology limit with
   the reflected functional, then close `ContDiff` by finite-order induction
   using `contDiff_succ_iff_hasFDerivAt` and `contDiff_clm_apply_iff`.  The
   normalized Euclidean bump substrate is now checked in
   `SCV/EuclideanWeylBump.lean`: normalized compact bumps, real-valued
   nonnegativity, support in `closedBall 0 ε`, and zero integral/compact
   support for differences.  The profile-scaling weighted-mass subpackage is
   now also checked in the same file, through Euclidean raw-integral scaling,
   one-variable weighted raw-mass scaling, and radius-independence of the
   normalized weighted mass.  The bump-subprofile support, plateau, and
   norm-equality facts are checked as well.  The first finite-interval radial
   Poisson substrate is now checked in `SCV/EuclideanWeylPoisson.lean`: radial
   mass and primitive definitions, the FTC derivative of radial mass, the
   global weighted-mass bridge from the checked `Ioi` mass to the finite ODE
   boundary condition, the near-zero mass formula, the linear primitive-derivative
   formula, the quadratic primitive profile at the origin, the away-from-zero
   radial ODE, the positive-radius scalar profile-Laplacian theorem, primitive
   vanishing outside the support radius, and the Euclidean origin
   smoothness/Laplacian theorem from the quadratic norm germ.  The off-origin
   Euclidean geometry layer is now checked through the cardinality/summation
   identities, the first Frechet derivative of the norm, the diagonal norm
   Hessian, the derivative of `y_i / ‖y‖`, the local first-derivative rewrite
   for `a ∘ ‖·‖`, the product-rule body of the radial second chain rule, the
	   off-origin profile Laplacian, the positive-half-line smoothness of the
	   radial primitive, the all-points theorem
	   `laplacian_radialPrimitiveProfile`, compact support and exact
	   topological-support radius of the norm-composed primitive, Schwartz
	   packaging, the positive-dimensional bump-difference primitive theorem
	   `exists_compact_laplacian_eq_euclideanWeylBump_sub_with_support`,
	   reflected-translate Laplacian commutation, and the harmonic bump
	   scale-invariance theorem `regularizedDistribution_bump_scale_eq`.  The
	   local ball-representative layer is now checked in
	   `SCV/EuclideanWeylRegularity.lean`: the half-margin and uniform-margin
	   closed-ball support lemmas, `euclideanWeylBallRepresentative`,
	   `euclideanWeylBallRepresentative_eq_regularized`,
	   `euclideanWeylBallRepresentative_eq_regularized_on_ball`,
	   `contDiffOn_euclideanWeylBallRepresentative`,
	   `euclideanConvolutionTest`, `euclideanConvolutionTest_apply`,
	   `euclideanConvolutionTest_apply_reflected`, and
	   `euclideanConvolutionTest_apply_reflectedTranslate`.  The remaining
	   Euclidean Weyl proof route now continues to the scalar
	   distribution-pairing identity and compact-support approximate-identity
	   representation assembly in `docs/scv_infrastructure_blueprint.md`.  The
	   pairing identity is now documented as a finite-probe/ordinary-Bochner
	   argument modelled on the checked `SCV/PaleyWiener.lean` probe
	   factorization, not as a forbidden `SchwartzMap`-valued Bochner integral.
	   The first probe slice is now explicit there and checked in
	   `SCV/EuclideanWeylProbe.lean`:
	   polynomial Euclidean weights, coordinate iterated line-derivative CLMs,
	   weighted bounded-continuous probes, the finite `euclideanProbeCLM`, and
	   the finite-dimensional domination theorem controlling
	   `SchwartzMap.seminorm` by those coordinate probes.  The Hahn-Banach
	   range factorization through this checked finite probe map is now checked
	   in the same file as
	   `euclideanSchwartzFunctional_exists_probe_factorization`, with the
	   supporting finite seminorm bound, probe-norm domination, kernel descent
	   to the probe range, and Hahn-Banach extension theorem all explicit.  The
	   componentwise Banach-valued probe integral identity and the compact-kernel
	   scalar pairing theorem are now checked in
	   `SCV/EuclideanWeylPairing.lean`: `euclideanPairingProbeFamily`,
	   compact-support integrability of that Banach-valued family,
	   `integral_euclideanPairingProbeFamily_eq_probe_convolution`, and
	   `regularizedDistribution_integral_pairing`.  The Euclidean
	   approximate-identity stage is now checked in
	   `SCV/EuclideanWeylApproxIdentity.lean`:
	   `euclideanConvolutionTest_apply_swap`,
	   `iteratedFDeriv_euclideanConvolutionTest_sub_eq_integral`,
	   `exists_weighted_iteratedFDeriv_euclideanTranslate_sub_le_linear`,
	   `tendsto_euclideanConvolutionTest_of_shrinking_normalized_support`, and
	   `exists_euclideanConvolutionTest_approxIdentity`.  The smaller-ball
	   representation theorem is now checked in
	   `SCV/EuclideanWeylRepresentation.lean` as
	   `euclidean_laplacian_distribution_regular_on_ball`, using the explicit
	   Weyl-bump sequence, scalar pairing, and constant-sequence limit
	   argument.  The next SCV subproblem is now the open-set representation
	   assembly.  The detailed route in
	   `docs/scv_infrastructure_blueprint.md` now uses the canonical Weyl ball
	   representative at each point and finite smooth partitions only on compact
	   test supports.  The remaining Lean work before the open theorem is:
	   support preservation for `χ * φ`, finite decomposition of a compactly
	   supported Schwartz test by partition functions, and the compact-support
	   integrability/finite-integral lemma for local continuous representatives.
	   These first prerequisites are now checked in
	   `SCV/EuclideanWeylOpen.lean`; the canonical-overlap lemma, smoothness of
	   the open representative, and finite compact `SmoothPartitionOfUnity`
	   bridge for `tsupport φ` are checked as well.  The ball-representation
	   theorem is now available in non-existential form as
	   `euclideanWeylBallRepresentative_represents_on_ball`.  The finite
	   summation identity and the full open-set theorem
	   `euclidean_weyl_laplacian_distribution_regular_on_open` are now checked
	   in `SCV/EuclideanWeylOpen.lean`.
	   Zero-dimensional bump-difference bookkeeping is only needed if a
	   dimension-free caller requires it.  The downstream complex-chart
	   holomorphic regularity layer is now checked in
	   `SCV/DistributionalEOWHolomorphic.lean`: the open-set Euclidean Weyl
	   theorem has been transported through `complexChartEuclideanCLE` as
	   `weyl_laplacian_distribution_regular_on_open`; the local fundamental
	   lemma for continuous-on-open functions tested against `SupportsInOpen`
	   Schwartz functions is checked; the real-smooth cutoff representative
	   with `dbar G = pointwiseDbar H` on `tsupport φ` is checked; distributional
	   `∂bar` holomorphy is converted to pointwise `pointwiseDbar = 0`; and the
	   finite-dimensional CR linear algebra now supplies
	   `differentiableOn_complex_of_contDiffOn_real_and_pointwiseDbar_zero`.
	   The final assembled theorem
	   `SCV.distributionalHolomorphic_regular` is checked with no new axioms or
	   sorrys.  The theorem-2 SCV frontier after Weyl/CR regularity moved to
	   regularized-envelope recovery, and that recovery layer is now checked
	   through the chart-assembly theorem below; the current frontier is local
	   continuous EOW extraction plus the upstream regularized-family/product-
	   kernel package.  The next small Lean bridge is now checked
	   as
	   `SCV.regularizedEnvelope_holomorphicDistribution_from_productKernel`:
	   combine product-kernel descent, the checked compact approximate identity,
	   the checked product-kernel `∂bar` consumer, and
	   `SCV.distributionalHolomorphic_regular` to obtain a holomorphic chart
	   representative for the descended distribution.  The delta-limit recovery
	   layer is now also checked in `SCV/DistributionalEOWKernelRecovery.lean`:
	   `eventually_translate_mem_open_of_shrinking_support`,
	   `integrable_continuousOn_realTranslate_mul_kernel`,
	   `regularizedEnvelope_difference_integral_identity_eventually`,
	   `regularizedEnvelope_kernelLimit_from_difference_integral`,
	   `regularizedEnvelope_kernelLimit_from_representation`,
	   `realMollifyLocal`, and
	   `regularizedEnvelope_deltaLimit_agreesOnWedges` together derive
	   `G (ψn n) z -> H z` from the actual representation integral and then
	   identify `H` with the plus/minus side functions by limit uniqueness.
	   The final checked SCV assembly theorem is now
	   `SCV.regularizedEnvelope_chartEnvelope_from_productKernel`: it applies
	   the checked product-kernel midpoint, derives the pointwise representation
	   of the recovered `H`, and then invokes the checked delta-limit wedge
	   agreement.  The remaining theorem-2 SCV frontier is therefore no longer
	   Weyl/regularity, the delta-limit estimate, or a free
	   pointwise-representation bridge; it is the local continuous EOW
	   extraction/patching and OS45 instantiation.  The bridge has been
	   decomposed and checked in `docs/scv_infrastructure_blueprint.md` through:
	   the now checked support theorem
	   `SCV.realConvolutionTest_supportsInOpen_of_translate_margin`, the now
	   checked continuity theorem
	   `SCV.continuousOn_realMollifyLocal_of_translate_margin`, the
	   checked compact-support Fubini/change-of-variables pairing theorem
	   `SCV.realConvolutionTest_pairing_eq_mollifier_pairing`, the checked
	   `SCV.regularizedEnvelope_pointwise_eq_of_test_integral_eq` endpoint, and
	   the checked supplier
	   `SCV.regularizedEnvelope_pointwiseRepresentation_of_productKernel`.
	   The first upstream regularized-family slice is now checked as well:
	   `SCV.localRealMollifySide_holomorphicOn_of_translate_margin` in
	   `SCV/LocalDistributionalEOW.lean`, proving local holomorphy of the
	   real-direction mollifier from the explicit support-translate margin.
	   The next boundary-extraction slice is also checked:
	   `SCV.regularizedBoundaryValue_continuousOn`,
	   `SCV.realMollifyLocal_eq_sliceIntegral_translate`,
	   `SCV.realMollifyLocal_eq_sliceFunctional`,
	   `SCV.exists_cutoffSliceIntegral_clm_of_continuousOn`,
	   `SCV.realMollifyLocal_eq_cutoffSliceCLM`,
	   `SCV.tendsto_cutoffSliceCLM_of_boundaryValue`,
	   `SCV.tendsto_mollified_boundary_of_clm`, and
	   `SCV.localRealMollify_commonContinuousBoundary_of_clm`.  These prove the
	   cutoff-local slice-CLM construction, evaluation of the cutoff CLM on the
	   translated mollifier kernel, convergence of those cutoff CLMs from the
	   raw distributional boundary-value hypothesis via
	   `SchwartzMap.smulLeftCLM`, and the Streater-Wightman regularized
		   common-boundary extraction.  The continuous-EOW extraction substrate is
		   now also public in `SCV/TubeDomainExtension.lean`:
		   `SCV.local_eow_extension` exposes the checked local Cauchy-polydisc
		   extension fields for global tube domains, and
		   `SCV.local_extensions_consistent` exposes the checked overlap
		   identity-theorem argument.  The local finite-dimensional geometry needed
		   to replace global tube membership is now checked in
		   `SCV/LocalContinuousEOW.lean`: the coefficient simplex, compact
		   chart-direction simplex, convex-cone inclusion, and positive-imaginary
		   normalization theorem
		   `SCV.localEOW_positive_imag_normalized_mem_simplex`.  The local
		   chart-membership replacements for the global `Phi_pos_in_tube` and
		   `Phi_neg_in_tube` steps are checked there as
		   `SCV.localEOW_chart_positive_polywedge_mem` and
		   `SCV.localEOW_chart_negative_polywedge_mem`, with the common-radius
		   two-sided package `SCV.localEOW_chart_twoSided_polywedge_mem`.  The
		   public chart-coordinate layer is checked as `SCV.localEOWRealChart`,
		   `SCV.localEOWChart`, `SCV.localEOWChart_real_imag`, and
		   `SCV.localEOWChart_twoSided_polywedge_mem`.  The remaining
		   theorem-2 supplier blocker is no longer an SCV splice.  It is the OS45
		   identity-order instantiation layer: the ordered seed is checked, but
		   the common-boundary theorem surface must be corrected before the
		   ordered horizontal-edge local wedge, compact-cutoff boundary CLM,
		   one-chart call, and side-component gluing can be implemented.  This is
		   not another distributional EOW theorem and not a wrapper.
	   The initial coordinate and trace-membership support
	   `BHW.configPermCLE`, `BHW.os45CommonChartCLE`,
	   `BHW.wickRotate_ordered_mem_acrOne`,
	   `BHW.adjacent_wick_traces_mem_acrOne`, and
	   `BHW.os45CommonChart_real_mem_pulledRealBranchDomain_pair`, together with
	   the direct-envelope packaging
	   `BHW.adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope`, is checked in
	   `OSToWightmanLocalityOS45CommonChart.lean` and
	   `OSToWightmanLocalityOS45TraceMembership.lean`.  This should now be read
	   as theorem-2 OS45 supplier plumbing, not as permission to redo
	   distributional EOW.  The pure SCV/distributional EOW infrastructure is an
	   existing input; the remaining theorem-2 task is to instantiate it in the
	   common OS45 chart and package the output as the concrete envelope consumed
	   by the checked direct-coordinate bridge.
	   The theorem-2 blueprint records the still-needed local supplier surfaces
	   `BHW.os45_adjacent_commonBoundaryEnvelope` and
	   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII`.  The old
	   target `SCV.local_distributional_edge_of_the_wedge_envelope` remains a
	   future global packaging theorem only; the current OS45 supplier consumes
	   the checked `SCV.chartDistributionalEOW_local_envelope` directly.  The
	   identity-order seed selection is now checked in
	   `BHW.choose_os45_identity_real_open_edge_for_adjacent_swap`, and the
	   same-patch domain/trace/geometry package is checked in
	   `BHW.os45_adjacent_identity_localEOWGeometry`.
	   `BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch`
	   supplies the Gram environment for that same `V`; and
	   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII` fills the
	   fields of `SelectedAdjacentDistributionalJostAnchorData` before the
	   already checked bridge constructs
	   `BHW.SourceDistributionalAdjacentTubeAnchor`.
   The theorem-2 blueprint now also gives the full scalar-coordinate
   Hall-Wightman source packet needed after those suppliers are available:
   checked Gram-permutation/domain definitions, the
   `SourceScalarRepresentativeData` package, the ordinary extended-tube scalar
   representative existence theorem, the compact-test-to-pointwise real-patch
   conversion, adjacent seed equality on the Gram environments, the
   scalar-overlap continuation theorem on `S''_n`, and the final Lean
   transcript closing
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`.
   The compact-test-to-pointwise conversion, adjacent seed equality,
   source-variety holomorphy under Gram-coordinate permutation, and the
   real-environment uniqueness theorem
   `sourceScalarRepresentative_adjacent_eq_on_overlap_of_realEnvironment` are
   checked in Lean as sorry-free support lemmas.  The final PET branch
   transcript has been moved back to proof-doc status because it depends on
   the remaining Hall-Wightman source obligations: the scalar representative
   existence theorem and the direct source single-valuedness theorem on
   `S''_n`.  Those obligations must not appear as production `sorry`s on the
   active import path.
   The source-overlap openness half is now also checked:
   `sourceAdjacentPermutationGramOverlap_relOpen`
   and `gramEnvironment_complexify_mem_adjacentOverlap` are in production Lean.
   The later audit changed the status of the generic witness/cover package:
   the enlargement from local overlap components to the full adjacent double
   scalar-product domain is not a consequence of the local anchor fields alone.
   It is source-equivalent unless supplied by a genuine global
   Hall-Wightman/Araki reachability or source single-valuedness theorem.
   Therefore the package around
   `exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain`,
   `mem_sourceAdjacentSeedCover_of_mem_doubleDomain`,
   `sourceAdjacentSeedCover_cover_doubleDomain`, and
   `sourceDoublePermutationGramDomain_adjacent_chain` is retained only as an
   archived proof-doc decomposition, not as an active production target.
   The step-1 realization input for that archived witness theorem is already
   fixed at the checked Lean surface
   `exists_sourceExtendedTube_realizations_of_mem_doubleDomain`.
   The latest doc pass also aligns the permutation side with the actual repo
   API: use concrete swaps and `BHW.Fin.Perm.adjSwap_induction` as the Lean
   surface, and keep abstract adjacent-transposition predicates only at the
   normalization boundary.
   For theorem 2 to be 100% implementation-ready, the direct source theorem
   must not remain one compressed theorem surface.  The proof docs now expose:
   1. real-environment uniqueness on one adjacent scalar overlap component,
      which is checked in `SourceExtension.lean`;
   2. the archived witness/cover decomposition that would reduce global
      Hall-Wightman reachability to overlap components;
   3. adjacent-transposition word propagation to a general permutation.
   The theorem-2 blueprint now contains Lean-shaped theorem surfaces and proof
   transcripts for the archived package, but those surfaces are not production
   implementation targets until the global source input is supplied.  The
   archived supplier names are:
   `SourceAdjacentOverlapWitness`,
   the witness fields `overlap_relOpen`, `overlap_connected`, and
   `environment_mem_overlap`,
   `sourceAdjacentSeedCover`,
   `sourceAdjacentPermutationGramOverlap_subset_seedCover`,
   `sourceAdjacentSeedCover_eq_union`,
   `exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain`,
   `mem_sourceAdjacentSeedCover_of_mem_doubleDomain`,
   `sourceAdjacentOverlapIndex_reflTransGen`,
   `sourceAdjacentSeedCover_cover_doubleDomain`,
   `sourceDoublePermutationGramDomain_adjacent_chain`, and
   `exists_sourceExtendedTube_realizations_of_mem_doubleDomain`.
   The theorem-2 blueprint now also records the intended proof route for that
   archived package:
   the adjacent overlap is the connected component of a Hall-Wightman
   real-environment neighbourhood intersected with the adjacent double scalar
   domain; the seed cover is the union of those overlap components; the chain
   theorem comes from the cover-reaching theorem
   `sourceAdjacentSeedCover_cover_doubleDomain` together with connected-union
   propagation via `IsConnected.biUnion_of_reflTransGen`;
   the normalization step from an abstract `IsAdjacentTransposition τ` to a
   concrete `Equiv.swap i ⟨i.val + 1, hi⟩` is fixed; and the step-1 input to
   witness construction would be the checked realization theorem
   `exists_sourceExtendedTube_realizations_of_mem_doubleDomain`.  The archived
   adjacent-word package remains available only as a possible later internal
   decomposition if the direct Hall-Wightman global continuation route needs
   it, not as part of the active theorem-2 contract.
   One more theorem-shape correction is now explicit: the final overlap object
   for this route cannot honestly remain parameter-free in `(d,n,π,i,hi)`
   alone. Because it is defined from a chosen Hall-Wightman local
   neighbourhood around `hAnchor.gramEnvironment π i hi`, the final code-level
   surface must depend on that chosen neighbourhood data, directly or through a
   packaged witness derived from `hAnchor` (and possibly `hRep`). The current
   production parameter-free constant should therefore be treated only as a
   placeholder, not as the final mathematical API.
   The route decision is now explicit: this adjacent-word package is archived
   as a possible internal decomposition only.  The endorsed theorem-2 contract
   is instead the direct global Hall-Wightman continuation theorem on the
   scalar-product domain, with the checked local overlap/real-environment
   theorem (A) as local support.  This fixes the live route and quarantines the
   old word-chain detour; the remaining live source frontier is
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
   not a production `sorry` for the source-equivalent witness theorem.
   Deep Research interaction
   `v1_ChdYZXp1YWRLRUJZMjlzT0lQa1BtbXlRNBIXWGV6dWFkS0VCWTI5c09JUGtQbW15UTQ`
   agrees with the local audit: this witness theorem is too strong from an
   arbitrary `SourceDistributionalAdjacentTubeAnchor` alone.  The proof docs are
   implementation-ready only after the missing input is made explicit as either
   a global adjacent double-domain connectedness/reachability theorem or the
   direct Hall-Wightman source single-valuedness theorem on `S''_n`.
   More precisely, if the archived witness theorem is later revived, its proof
   docs must expose the Hall-Wightman local-neighbourhood selection step in
   Lean-shaped form:
   1. choose extended-tube realizations for `Z` and `τ · Z`;
   2. extract the relevant real boundary/environment data from those
      realizations;
   3. select a Hall-Wightman scalar-variety neighbourhood around that real
      data;
   4. identify the corresponding anchor label `π`;
   5. package the resulting connected overlap component as
      `SourceAdjacentOverlapWitness`.
   The correct active packaging remains two-stage:
   `SourceScalarRepresentativeData` is
   local branch data on `sourceExtendedTubeGramDomain d n`, while the global
   Hall-Wightman theorem on `M_n` / `S''_n` is the later continuation theorem
   for that branch.  The docs should not blur those two roles.
   After the latest source audit, the docs no longer treat connectedness of
   the full adjacent double scalar-product domain as automatic.  The active
   local-overlap object is the `overlap` field in
   `SourceAdjacentOverlapWitness`; the legacy parameter-free
   `sourceAdjacentPermutationGramOverlap` remains only the full adjacent double
   domain helper used by older checked support lemmas.  The seed-cover / chain
   machinery is archived unless the missing global source input is supplied.  A
   future collapse of the witness overlap to the full adjacent double domain
   would be an optimization only after a separate proof justifies it.
   One more tempting shortcut has now been ruled out explicitly: the scalar
   double-domain is not automatically the Gram-map image of the vector-valued
   adjacent overlap domain, because `sourceDoublePermutationGramDomain`
   remembers separate realizability of `Z` and `τ·Z`, not realizability by one
   common configuration `w` with both `w` and `τ·w` in `ExtendedTube`.
   Likewise, the scalar double-domain should not be treated as obviously
   conjugation-equivariant under permutation of Gram coordinates, since
   `sourceExtendedTubeGramDomain` itself is not permutation-invariant.
5. Streater-Wightman Theorem 2-11 has now been audited as another statement of
   the BHW analytic-continuation theorem, not as a source for the missing
   active-gallery theorem. Streater-Wightman Figure 2-4 remains only the
   adjacent common-real-environment input; it does not supply a global finite
   chamber gallery.
6. Jost, *The general theory of quantized fields*, p. 83, second theorem, has
   been page-audited in the local image PDF. It is the OS I §4.5 boundary
   locality theorem: Wightman properties except locality plus total symmetry
   imply locality. The remaining Slot-10 work is the Lean translation into the
   canonical-shell pairing theorem, not source identification.
7. The theorem-2 Slot-6/Slot-7 interface no longer has two active branches.
   The active Lean branch is the source-backed BHW single-valuedness packet:
   use checked local source support from
   `BHWPermutation/SourceExtension.lean`, then prove or source-import
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
   and feed its sector-equality corollary to
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.
   The common-forward-tube fixed-orbit gallery remains retired, because a
   common Lorentz witness for two ordinary permuted forward-tube chambers
   forces the labels to be equal.  The reachable-label `hOrbit` monodromy
   theorem remains conditional infrastructure, not the theorem-2 gate.  The
   locality-assuming top-level `BHW.bargmann_hall_wightman_theorem` is not an
   allowed replacement.

## 1. What "100% implementation-ready" means

A proof doc counts as complete only when all of the following are true.

1. The theorem route is unique.
   There is one endorsed theorem path, and alternate routes are either deleted
   or explicitly quarantined.
2. The theorem surfaces are fixed.
   The named theorem packages are part of the implementation contract, not loose
   suggestions.
3. The helper-theorem packaging is fixed.
   If the later Lean code is allowed a packaging convenience, the exact allowed
   form is documented.
4. The proof transcript is explicit.
   The doc says which theorem is proved first, which theorem consumes it next,
   and how the proof moves mathematically from one to the next.
5. Existing repo consumers are named exactly.
   The doc does not say "use existing infrastructure"; it says which theorem
   names are consumed.
6. Representation constraints are explicit.
   If the current Lean encoding differs from the paper-level language, the doc
   says exactly how the implementation should adapt without changing the route.
7. Historical alternatives are fenced off.
   Earlier false routes, wrapper-heavy routes, or broader theorem surfaces are
   marked as forbidden rather than left as optional memory.
8. Exit criteria are checkable.
   The doc can be audited by search for unresolved wording and by theorem-name
   cross-checks.

## 2. Global completion protocol

Every proof-doc completion pass should follow this order.

1. Search for tentative wording:
   - `candidate`
   - `if needed`
   - `if easiest`
   - `may shift`
   - `placeholder`
   - `future theorem slot`
   - `fallback`
   - `later Lean`
2. Classify each hit as:
   - acceptable implementation commentary,
   - harmless historical note,
   - or a real mathematical/documentation gap.
3. For every real gap:
   - fix the route,
   - fix the theorem names,
   - fix the proof-package order,
   - update the global triage docs.
4. Re-audit the nearest downstream and upstream docs so the fix does not leave
   inconsistent language elsewhere.
5. Record any production-relevant doc change in `agents_chat.md` append-only.

## 3. Completion order for the remaining docs

The remaining hardening work should proceed in this order.

### Phase A. Active OS-route frontiers

These are the highest-priority docs because Claude’s production work depends on
them directly.

1. `docs/theorem3_os_route_blueprint.md`
2. `docs/theorem2_locality_blueprint.md`
3. `docs/theorem4_cluster_blueprint.md`
4. `docs/sorry_triage.md`
5. `docs/mathlib_gap_analysis.md`

Completion criterion for Phase A:

1. theorem 2/3/4 each have exactly one endorsed route;
2. each package theorem has a fixed name;
3. each doc explicitly identifies which existing production theorems are
   consumers and which new theorem packages are still missing;
4. no route-level wording still allows fallback to discarded shells, K2
   wrappers, or raw-topology restarts.

### Phase B. Core analysis support

These docs control the mathematical suppliers for theorem 2/3 and general `k`.

1. `docs/scv_infrastructure_blueprint.md`
2. `docs/nuclear_spaces_blueprint.md`
3. `docs/general_k_continuation_blueprint.md`
4. `docs/os1_detailed_proof_audit.md`
5. `docs/os2_detailed_proof_audit.md`

Completion criterion for Phase B:

1. every SCV supplier is broken into theorem packages rather than invoked as
   "SCV machinery";
2. the nuclear-space doc has one endorsed route and a blocked-only fallback;
3. the general-`k` doc fixes file boundaries, theorem slots, indexing, and SCV
   imports before implementation;
4. OS I / OS II audit docs point to exact local theorem-package suppliers and
   no longer leave hidden paper steps implicit.

### Phase C. Downstream reconstruction side lanes

These docs should be hardened after Phases A-B because they consume A-B.

1. `docs/gns_pipeline_blueprint.md`
2. `docs/wightman_uniqueness_blueprint.md`
3. `docs/r_to_e_blueprint.md`
4. `docs/bhw_permutation_blueprint.md`

Completion criterion for Phase C:

1. no theorem surface is still described as "should be possible once...";
2. SCV/nuclear inputs are named exactly;
3. no reverse-direction positivity argument quietly reuses a forward theorem;
4. uniqueness and permutation packages state exact dependency order.

### Phase D. Operator-algebra side backlog

These should be documented precisely, but remain lower priority than A-C.

1. `docs/vna_infrastructure_blueprint.md`
2. `docs/vna_triage.md`

Completion criterion for Phase D:

1. the Stone/spectral route is fixed at the theorem-package level;
2. predual/KMS/modular packages no longer blur foundational and consumer layers;
3. the first theorem to implement in each file is fixed.

## 4. File-by-file acceptance criteria

## 4.1. `theorem3_os_route_blueprint.md`

This doc is complete only when:

1. Package A through Package I each have fixed theorem names;
2. Package C is explicitly marked as false legacy infrastructure, not as a live
   theorem with an active proof strategy;
3. Package I is stated on the corrected Section 4.3 transformed-image theorem
   surface, with the transport codomain on the Section-4.3 half-space
   Schwartz side rather than either
   a support restriction `tsupport ⊆ PositiveEnergyRegion` or a false
   `DenseRange` claim in full `SchwartzNPoint d n`;
4. Package I has concrete theorem slots for the explicit `(4.19)`-`(4.20)`
   test-function transform, the transformed image, its half-space dense-range
   paper theorem, the transport map on that image, the quadratic identity
   there, and the final public closure theorem;
5. any surviving mention of Packages F/G/H is clearly marked as withdrawn /
   historical, not endorsed implementation guidance;
6. the exact legacy-consumer status after Package C is named;
7. the branch-`3b` support route is fixed at the concrete
   `PartialFourierSpatial.lean` companion-file level rather than the withdrawn
   abstract Schwartz-helper route;
8. the support-work checklist is satisfied literally.

## 4.2. `theorem2_locality_blueprint.md`

This doc is complete only when:

1. the active route is uniquely the OS II / OS I §4.5 branch-difference path:
   selected Figure-2-4 source patch, branchwise horizontal source germs,
   branch BV packets, local EOW envelope, BHW/Jost source continuation, and
   final OS-II boundary transfer to `bvt_W`;
2. the source layer is fixed at the oriented packet family named in the fork
   compatibility guard, because theorem 2 follows OS I §4.5's proper-complex
   `L_+(C)` continuation.  The pure-Gram scalar-packet surfaces
   `BHW.OS45OneBranchScalarGramEqPacket`,
   `BHW.os45OneBranchScalarGramEq_sourceInput_id`, and
   `BHW.os45OneBranchScalarGramEq_sourceInput_adjacent` are conditional side
   surfaces only after a full-component Hall-Wightman source gate is closed.
   A mixed packet family is disallowed, and there is no public arbitrary-`β`
   geometry-only source theorem;
3. the Figure-2-4 selector is source-ready and closure-ready: `Ufig` and
   `Upath` share one anchor, the ordered seed is chosen inside
   `Ufig ∩ Upath`, the exported open-chart canonical field is
   `hV_adjLift_ET`, and the exported closure path field on the active route is
   the oriented field `hV_orientedPath_closure`; the older pure-Gram
   `hV_figPath_closure` is retained only as checked geometric support;
4. the branch-BV and local EOW theorem surfaces name the exact CLMs, side
   wedges, chart-linear kernel pushforwards, and gluing consumers, without
   treating the local boundary functional as `bvt_W`;
5. the downstream Hall-Wightman/Jost and final boundary-transfer slots identify
   which theorem packages consume the local EOW output and where the physical
   `bvt_W` distribution re-enters;
6. every historical shortcut is fenced off: pointwise horizontal equality,
   quarter-turn bypass, boundary-functional demotion, generic PET branch
   independence, and the archived adjacent-word source cover are not active
   implementation options;
7. the active oriented scalar-source packet separates checked source-germ
   infrastructure from the remaining producer theorems:
   `BHW.same_sourceOrientedInvariant_detOneOrbit_or_singularLimit`,
   `BHW.extendedTube_same_sourceOrientedInvariant_extendF_eq`,
   checked `BHW.sourceOrientedExtendedTubeDomain_relOpen_connected`,
   `BHW.sourceOrientedVarietyGermHolomorphicOn_extendF_descent`,
   `BHW.sourceOrientedScalarRepresentativeData_of_branchLaw`,
   `BHW.hallWightman_sourceOrientedScalarRepresentativeData`, and
   `BHW.sourceOrientedScalarRepresentativeData_bvt_F`; each active producer
   name must have a complete proof transcript, its exact lower support
   dependencies, and an explicit first Lean target.  If a name has only an
   explicit "not Lean-ready" status, this checklist item is not yet complete.
   The first four producer surfaces must also carry their component ledgers:
   determinant-sensitive oriented branch law, Lemma-3 oriented local
   realization, regular/removable holomorphic descent, invariant-ring
   normality, and Figure-2-4 oriented path provenance.  The ordinary
   pure-Gram packet remains a conditional side packet only if the separate
   full-component/improper Hall-Wightman source input for `bvt_F` is
   sourced/proved;
8. the oriented adjacent `S'_n` packet keeps the canonical compact-boundary
   producer, the OS-free Jost/Ruelle theorem, the oriented real-patch seed
   data, and the Figure-2-4 oriented scalar path/corridor in non-circular
   order, with the exact `Path.trans`/`JoinedIn` API pinned and no dependency
   on final locality, global PET branch independence,
   `AdjacentOSEOWDifferenceEnvelope`, or a local boundary functional demotion.
   Its compact real patch must be the point-permuted source PET-overlap patch;
   the half-time common edge may appear only as a separate contact/provenance
   field and never as the domain on which raw `extendF` continuity is assumed.

## 4.3. `theorem4_cluster_blueprint.md`

This doc is complete only when:

1. theorem-3-to-one-factor extraction is spelled out through exact theorem
   names;
2. `normalizedZeroDegreeRightVector` has a literal definition and structural
   lemmas;
3. theorem-package names are fixed, not illustrative;
4. theorem 4 is visibly pure consumer work after theorem 3.

## 4.4. `general_k_continuation_blueprint.md`

This doc is complete only when:

1. every Chapter V / VI package has a fixed theorem-slot inventory;
2. the envelope/Malgrange-Zerner step is explicit and not a black box;
3. file boundaries and import order are fixed;
4. the SCV dependency surface is named exactly;
5. the trusted-vs-untrusted checklist is explicit.

## 4.5. `scv_infrastructure_blueprint.md`

This doc is complete only when:

1. the one-point forward-tube package has an explicit proof transcript;
2. the flattened regular constructor route is fixed;
3. Vladimirov-Tillmann and Bochner packages are split into real theorem
   packages;
4. no consumer doc needs to invent its own boundary-value constructor.

## 5. Audit queries that must return clean

Before declaring the proof docs complete, rerun searches like:

```text
rg -n "candidate route|if easiest|may shift|future theorem slot|primary route|fallback route|placeholder" docs/*.md
```

and manually justify every remaining hit.

Also rerun theorem-name cross-checks against the live code for:

1. theorem 2 consumer theorems,
2. theorem 3 consumer chain,
3. theorem 4 extraction theorems,
4. SCV one-point constructors,
5. GNS matrix-coefficient bridge dependencies.

## 6. Definition of done

The proof-doc stack is complete only when:

1. every active frontier theorem has one endorsed route;
2. every side-lane theorem package has fixed names or an explicitly quarantined
   blocked-only fallback;
3. the global docs (`sorry_triage.md`, `mathlib_gap_analysis.md`) agree with
   the per-theorem blueprints;
4. production work can proceed by proving named theorem packages rather than by
   making fresh mathematical choices.
5. every named external theorem is separated into source-backed content and any
   additional derived formalization obligation, with no derived obligation
   mislabeled as a verbatim paper theorem.
