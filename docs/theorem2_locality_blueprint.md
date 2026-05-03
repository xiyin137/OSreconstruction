# Theorem 2 Locality Blueprint

Purpose: this note is the active implementation blueprint for the live
theorem-2 `E -> R` locality frontier

- `OSToWightmanBoundaryValues.lean`, private theorem
  `bvt_W_swap_pairing_of_spacelike`.

This note is intentionally narrow. It records only the current OS-paper route.
The retired finite-shell / arbitrary-transposition route is not part of the
implementation plan anymore and should not be revived.
There is no alternate active route. The only exception that could justify a
route change would be an explicit OS-paper error documented locally first; no
such exception is in scope here.

This note should be read together with
[`bhw_permutation_blueprint.md`](/Users/xiyin/OSReconstruction/docs/bhw_permutation_blueprint.md).
That sibling note owns the BHW permutation-geometry obligations and records why
the former fixed-`w` forward-tube chamber-chain route is quarantined.  The
present note owns the theorem-2 consumer chain from the OS45 local edge packet
to the final `bvt_W` locality theorem.

Current BHW interface correction: the **common fixed-`w`
permuted-forward-tube gallery** is rejected, and the reachable-label `hOrbit`
monodromy route is no longer the strict OS-paper implementation gate.  The
latest theorem-shape audit agrees that fixed-`w` ordinary permuted
forward-tube overlaps are impossible, but also warns that `hOrbit` is a custom
pointwise complex-Lorentz-orbit stratification theorem, not the
Hall-Wightman/BHW single-valuedness theorem used in OS I Section 4.5.  The
strict theorem-2 route is therefore the direct source-backed BHW
single-valuedness packet on the permuted extended tube `S''_n`.  This
correction is recorded from the local theorem-shape audit and Gemini Deep
Research interaction
`v1_ChZjT1h1YWRpZUU1LThfdU1QMi1LRGVBEhZjT1h1YWRpZUU1LThfdU1QMi1LRGVB`.

Current critical-path ledger for the `2 <= d` implementation:

1. construct `SelectedAdjacentDistributionalJostAnchorData OS lgc n` from the
   OS45 local common-chart/EOW packet plus the Hall-Wightman scalar-product
   real-environment theorem for the chosen Jost patch;
2. project that data to
   `BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n (bvt_F OS lgc n)`
   by the checked bridge
   `bvt_F_distributionalJostAnchor_of_selectedJostData`;
3. use `BHWPermutation/SourceExtension.lean` only for checked local source
   support.  The real-environment uniqueness step
   `sourceScalarRepresentative_adjacent_eq_on_overlap_of_realEnvironment` is now
   checked in production Lean.  The former generic witness/cover theorem
   `exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain` has been retired
   from production because it is source-equivalent, not a consequence of the
   local anchor fields alone;
4. prove or explicitly source-import the source-backed Hall-Wightman
   compatibility theorem
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
   then use the already documented PET-algebra assembly
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` and sector
   equality
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry`;
5. specialize to `bvt_F OS lgc n` as
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`, then do the final
   Jost-boundary transfer to locality.

The checked selected-adjacent monodromy consumer
`bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData` may remain as
conditional infrastructure.  It should not be treated as the theorem-2 gate
unless the extra `hOrbit` theorem is separately proved and accepted as a
faithful decomposition of the Hall-Wightman source theorem.

## 0. Paper authority and OS II correction

The implementation route in this file must follow the OS papers strictly.  OS
I Section 4.5 supplies the locality skeleton only after the reconstructed
analytic Wightman boundary values have been built on the corrected OS II route.

The only admitted correction to the printed OS route is the known OS I Lemma
8.8 failure.  Any theorem-2 step that depends, directly or indirectly, on the
many-variable analytic continuation or its growth/temperedness estimates must
use the OS II replacement:

1. OS II Chapter V for the corrected induction/local analytic continuation;
2. OS II Chapter VI for the growth and tempered boundary-value estimates;
3. the repo's `OSLinearGrowthCondition` / `bvt_F` construction only as the
   Lean-facing packaging of that OS II repair.

Therefore references below to OS I formulas such as `(4.12)` or to the
permuted continuation `S'_n` must be read as using the OS-II-corrected
continuation object, not the false OS I Lemma 8.8 shortcut.  No alternative
route, weakened theorem surface, same-test Euclidean/Minkowski equality, or
generic BHW permutation-flow shortcut is allowed unless a new OS-paper error is
identified and documented locally first.

## 0.1. Docs-first gate for theorem 2

This file is currently the active theorem-2 proof gate. Production Lean should
not move past the already-scoped support files until the following mathematical
inputs are explicit enough to be reviewed line-by-line against the local
references:

1. **Slot 6 source-backed BHW single-valuedness.** The active theorem packet
   is still the OS I §4.5 / Hall-Wightman packet on the permuted extended
   tube, but the current generic Lean statement
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`
   is **not** implementation-ready with only
   `hF_holo`, `hF_lorentz`, and total `hF_perm`.  The approved Deep Research
   audit and the local `BHWReducedExtension.lean` warning both identify the
   same issue: total off-domain values of a Lean function can make
   `hF_perm` hold without constraining the analytic germ on the ordered
   forward tube.  The production surface must therefore be refactored before
   the remaining `sorry` is closed.  The allowed refactor is either the
   distributional Euclidean/Jost-anchored Hall-Wightman/EOW theorem documented
   in Section 4 below, or the OS-specific selected-edge specialization that
   supplies that anchor from the OS-II-corrected `bvt_F` construction.  Once
   that source surface is fixed, the active Lean consumer is the direct
   source-backed BHW single-valuedness theorem on `S''_n`, not the
   reachable-label `hOrbit` decomposition.  The rejected object is the older
   common fixed-`w` **permuted forward-tube** gallery: its proposed edges
   require one transformed point to lie in two distinct ordinary permuted
   forward tubes, while the repository already proves
   `BHW.permutedForwardTube_sector_eq_of_mem` and
   `BHW.forwardTube_inter_permutedForwardTube_eq_empty_of_ne_one`.  The
   reachable-label `hOrbit` theorem is weaker than the rejected common-witness
   gallery, but it is still an extra pointwise orbit-stratification theorem and
   is not supplied by OS I §4.5 or Hall-Wightman as the locality proof is
   written.
2. **Slot 10 BHW/Jost boundary packet.** The `S'_n` and `S''_n` representations
   are fixed below as `BHW.PermutedForwardTube d n π` and
   `BHW.PermutedExtendedTube d n`, with sectors
   `BHW.permutedExtendedTubeSector d n π`. The single-valued continuation on
   `S''_n` is supplied by the Slot 7 branch-independence theorem, and the
   boundary-value consumer is the existing
   `bv_local_commutativity_transfer_of_swap_pairing`. The remaining hard
   theorem surface is
   `bvt_F_jostBoundary_pairing_of_spacelike_of_two_le`.
3. **Dimension-one complex-edge packet.** The `d = 1` lane is now reduced to the
   one-gap data theorem
   `d1_acrOne_complexEdgeData_of_permutedExtendedTubeSector`; the downstream
   zero-on-chart, PET-evaluation, and adjacent-sector compatibility steps are
   mechanical consumers of that data plus the existing identity-theorem
   infrastructure. It must not reuse the circular generic permutation-flow
   blocker.

The verified paper facts currently used are narrower than the remaining Lean
surfaces:

- OS I Section 4.5 fixes the order
  `symmetry -> analytic continuation on S'_n -> BHW enlargement on S''_n ->
  Jost boundary locality`.
- Streater-Wightman Figure 2-4 gives the adjacent common real environment for
  neighboring permuted extended tubes.
- Streater-Wightman Theorem 3-6 is **not** a theorem-2 input: its proof uses
  local commutativity, which is exactly what theorem 2 is proving. It may only
  be used as bibliographic orientation for the standard terminology around
  permuted Wightman functions, not as a proof supplier.
- The local Hall-Wightman scan supports the BHW extended-tube continuation and
  single-valuedness input for Slot 6.  It does not support a fixed-`w`
  forward-tube overlap gallery, and the Lean definitions make such overlap
  edges empty for distinct sector labels.
- The local Jost source has been page-audited for the Slot-10 boundary theorem:
  `references/general-theory-of-quantized-fields.pdf`, PDF page `49`, right
  half, printed page `83`, contains the second theorem cited by OS I. It says
  that a Wightman function with all Wightman properties except those derived
  from locality, and with the required symmetry, satisfies locality.
- The local Streater-Wightman source has been checked for the distributional
  EOW ingredient: `references/pct-spin-and-statistics-and-all-that-9781400884230_compress.pdf`,
  Theorem 2-16 (printed pp. `81-83`) proves the distributional EOW theorem by
  real-variable test-function regularization, continuous EOW, a
  Schwartz-nuclear-kernel argument, translation covariance, and a delta
  sequence.  This is the theorem shape used by the SCV blueprint.  Theorem
  2-17 is only the zero-boundary uniqueness corollary and does not replace the
  local envelope needed for `AdjacentOSEOWDifferenceEnvelope`.

## 1. Final theorem surface

The live frontier is the adjacent boundary-distributional statement:

```lean
private theorem bvt_W_swap_pairing_of_spacelike
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 ->
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) ->
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ->
      bvt_W OS lgc n f = bvt_W OS lgc n g
```

This matches the corrected core locality surface
`IsLocallyCommutativeWeak` in
`Wightman/Reconstruction/Core.lean`.

## 2. Paper route

The proof must follow OS I Section 4.5 exactly. In the local OCR of
`references/Reconstruction theorem I.pdf`, Section `4.5. Locality` on page `97`
says:

1. symmetry together with Eqs. `(4.1)`, `(4.12)`, and `(4.14)` gives a
   symmetric analytic continuation into the permuted forward-tube domain
   `S'_n`;
2. the Bargmann-Hall-Wightman theorem enlarges that continuation to the
   complex-Lorentz saturation `S''_n`;
3. the cited Jost theorem (`Ref. [12]`, p. `83`, second theorem in the local
   OCR text) yields locality of the boundary distributions.

The local proof-audit in
[`os1_detailed_proof_audit.md`](/Users/xiyin/OSReconstruction/docs/os1_detailed_proof_audit.md)
Section `9` / `9.1` fixes the safe Lean-facing interpretation: theorem 2 is a
branch-difference argument, not a same-shell Wick-to-real equality.

1. **OS-II repaired symmetry layer.**
   Use the reconstructed OS-II analytic continuation package
   `bvt_F_acrOne_package` as the Lean-facing form of the OS §4.5 symmetry input.
   The older checked theorem
   `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector` remains the compact
   E3/Wick sanity check on ordered real patches, but the active adjacent-edge
   consumer proves Wick-trace zero directly from the permutation symmetry field
   of `bvt_F_acrOne_package`.

2. **Local common-boundary / EOW layer.**
   Near a real adjacent Jost edge point, realize the same adjacent
   branch-difference object on a common local chart.  Slot 1 supplies the
   common-chart envelope; the already checked
   `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` consumer
   then continues Wick-trace zero to the real Jost edge.

3. **Distributional Jost-anchor packaging.**
   Package the resulting compact-test equality on one real-open Jost slice
   together with the Hall-Wightman scalar-product real environment as
   `SelectedAdjacentDistributionalJostAnchorData`, then pass it through the
   already checked bridge
   `bvt_F_distributionalJostAnchor_of_selectedJostData`.

4. **Checked PET/BHW branch-gluing layer.**
   Feed the adjacent selected data into the already-checked selected-branch and
   PET gluing theorems.

5. **Boundary transfer.**
   Use the existing boundary-value transfer theorems to identify the resulting
   boundary distributions with `bvt_W OS lgc` and close the adjacent locality
   theorem.

Nothing in this route should appeal to:

- finite-height canonical-shell equality,
- an arbitrary transposition primitive theorem,
- a one-branch Wick-to-real comparison,
- a theorem stating locality for a prepackaged `WightmanFunctions` output.

Every theorem slot below must be read as a Lean packaging of one of those OS
paper steps, not as permission to insert a different proof route.

## 3. Already checked production hooks

The following theorems are already in production and are the only allowed local
inputs for the supplier chain.

### 3.1. Real adjacent-overlap and OS45 geometry

In `ComplexLieGroups/AdjacentOverlapWitness.lean`:

- `adjacent_overlap_real_jost_witness_exists`

In `Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45.lean`:

- `choose_os45_real_open_edge_for_adjacent_swap`
- `choose_os45_real_open_edge_for_adjacent_swap_with_domains`
- `os45_adjacent_localEOWGeometry`
- `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`
- `AdjacentOSEOWDifferenceEnvelope`
- `bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`

In
`Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45TraceMembership.lean`:

- `adjacent_wick_traces_mem_acrOne`
- `os45CommonChart_real_mem_pulledRealBranchDomain_pair`
- `adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope`

In `Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45Bridge.lean`:

- `adjacentOS45RealEdgeDifference`
- `adjacentOS45RealEdgeDifference_holomorphicOn`
- `adjacentOS45RealEdgeDifference_continuousOn`
- `adjacentOS45RealEdgeDifference_realEmbed_continuousOn`

In `Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45CommonEdge.lean`:

- `os45CommonEdgeRealCLE`
- `choose_os45_common_real_edge_for_adjacent_swap`

### 3.2. Selected-witness / PET-side consumers

In `Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean`:

- `SelectedAdjacentDistributionalJostAnchorData`
- `bvt_F_distributionalJostAnchor_of_selectedJostData`
- `SelectedAdjacentPermutationEdgeData`
- `bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`
- `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`

The active theorem-2 OS-side supplier targets
`SelectedAdjacentDistributionalJostAnchorData`: it records the chosen OS45
Jost patch, compact-test adjacent boundary equality, both real ET membership
facts, and the scalar-product real environment.  The immediate strict-OS
consumer is its checked projection to
`BHW.SourceDistributionalAdjacentTubeAnchor`, which supplies the
source-backed Hall-Wightman theorem.  Its projection to
`SelectedAdjacentPermutationEdgeData` remains useful for the conditional
selected-adjacent monodromy route, but that route is no longer the theorem-2
gate.

### 3.3. Checked PET gluing / monodromy / boundary-transfer algebra

In `ComplexLieGroups/Connectedness/PermutedTubeGluing.lean`:

- `BHW.gluedPETValue`
- `BHW.gluedPETValue_eq_of_mem_sector`
- `BHW.gluedPETValue_holomorphicOn`

In `ComplexLieGroups/Connectedness/PermutedTubeMonodromy.lean`:

- `BHW.petReachableLabelSet_adjacent_connected_of_orbitChamberConnected`
- `BHW.petSectorFiber_adjacent_connected_of_reachableLabelConnected`
- `BHW.extendF_pet_branch_independence_of_adjacent_of_reachableLabelConnected`
- `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`
- `BHW.extendF_perm_eq_on_extendedTube_of_petBranchIndependence`
- `BHW.F_permutation_invariance_of_petBranchIndependence`

In `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean`:

- `bv_local_commutativity_transfer_of_swap_pairing`

These files are checked algebra and conditional infrastructure.  They are
**not** a license to skip the missing BHW/Jost source theorem.  In particular:

1. `PermutedTubeGluing.lean` assumes all-overlap compatibility on PET; it does
   not create that compatibility from adjacent data.
2. `PermutedTubeMonodromy.lean` reduces adjacent compatibility to all-overlap
   compatibility **once** the extra fixed-fiber / reachable-label geometry is
   supplied; that geometry is not an OS-paper substitute for the source-backed
   Hall-Wightman theorem.
3. theorem 2 must not route through the generic
   `PermutationFlow.iterated_eow_permutation_extension` consumer, because the
   latter mixes in the deferred dimension-one blocker
   `blocker_iterated_eow_hExtPerm_d1_nontrivial`.

## 4. Exact remaining theorem slots for `2 <= d`

The strict active `2 <= d` route begins with the OS45 source supplier in Slot
1 and then proceeds to the source-backed Hall-Wightman packet documented in
Sections 4.4-4.8 below.  The selected-adjacent monodromy slots retained in
this section are conditional checked infrastructure: they are useful
consumers, but they are not the OS-paper theorem-2 gate unless `hOrbit` is
proved as a separate theorem and explicitly accepted as a faithful
decomposition of Hall-Wightman.

### Slot 1. `os45_adjacent_singleChart_commonBoundaryValue`

This is the first genuinely unproved theorem on the active route.

```lean
theorem os45_adjacent_singleChart_commonBoundaryValue
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (V : Set (NPointDomain d n)) (rho : Equiv.Perm (Fin n)),
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
      (∀ x ∈ V, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
      AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
        (Equiv.swap i ⟨i.val + 1, hi⟩) V
```

Mathematical content:

- choose `V` and `rho` from `os45_adjacent_localEOWGeometry`;
- export the Jost and both adjacent extended-tube membership facts for this
  **same** `V`; these side conditions must not be reselected later from a
  separate call to the geometry theorem;
- use the OS45 quarter-turn / common-edge geometry only to choose a connected
  local complex domain `U` around the selected edge where both the Wick trace
  and the real-edge trace live;
- define the honest adjacent branch-difference object on the real edge by the
  natural adjacent real-edge difference

  ```lean
  H_-(z) :=
    BHW.extendF (bvt_F OS lgc n)
      (BHW.permAct (Equiv.swap i ip1) z) -
    BHW.extendF (bvt_F OS lgc n) z
  ```

  i.e. `adjacentOS45RealEdgeDifference`;
- use local common-boundary / EOW to construct one common holomorphic
  branch-difference object on `U`;
- prove that its Wick trace is the direct adjacent `bvt_F` difference

  ```lean
  bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k))) -
    bvt_F OS lgc n (fun k => wickRotatePoint (x k))
  ```

  and that its real trace is the direct adjacent `extendF` difference above;
- package those trace identities as an `AdjacentOSEOWDifferenceEnvelope`.

Slot 1 deliberately does **not** prove the branch difference is zero.  The
checked consumer
`BHW.bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`
uses the Wick trace field together with the permutation-symmetry field of
`bvt_F_acrOne_package` to prove Wick-side zero, then applies the already checked
distributional Wick-section identity theorem
`eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` to transport
that zero to the real edge.

This theorem is where the actual OS I §4.5 local common-boundary argument lives.
It is not a replacement for the paper route; it is the local chart-level
formalization of the OS branch-difference step.

Checked support already available for Slot 1 after checkpoint `1ad959e` and
the later checked coordinate-packaging pass:

- `os45PulledRealBranch`
- `os45PulledRealBranch_holomorphicOn`
- `os45PulledRealBranch_apply_realBranch`
- `os45QuarterTurnConfig_reindexed_realBranch_eq`
- `os45PulledRealBranch_apply_reindexed_commonPoint`
- `os45PulledRealBranch_sub_eq_adjacentOS45RealEdgeDifference`
- `adjacent_wick_traces_mem_acrOne`
- `os45CommonChart_real_mem_pulledRealBranchDomain_pair`
- `adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope`

These theorems live in
`OSToWightmanLocalityOS45BranchPullback.lean` and
`OSToWightmanLocalityOS45TraceMembership.lean`.  Their role is precise:
they provide the two trace-membership calculations, a non-tautological
common-chart representation of the negative-side real branch difference, and a
checked pullback from a common-chart envelope to the direct-coordinate
`AdjacentOSEOWDifferenceEnvelope`.  They do **not** close Slot 1 by themselves:
the genuine OS45 common-boundary theorem still has to construct the common
connected chart and holomorphic function.

Exact Lean-shaped use of the branch-pullback support:

```lean
let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
let Pid :=
  BHW.os45PulledRealBranch (d := d) (n := n) OS lgc ρ
let Pswap :=
  BHW.os45PulledRealBranch (d := d) (n := n) OS lgc (τ.symm * ρ)

have hcommonPoint :
    os45QuarterTurnConfig
        (fun k => BHW.realEmbed (fun j => x (τ j)) ((τ.symm * ρ) k)) =
      os45QuarterTurnConfig (fun k => BHW.realEmbed x (ρ k)) := by
  simpa using
    BHW.os45QuarterTurnConfig_reindexed_realBranch_eq
      (d := d) (n := n) τ ρ x

have hrealDiff :
    Pswap (os45QuarterTurnConfig (fun k => BHW.realEmbed x (ρ k))) -
      Pid (os45QuarterTurnConfig (fun k => BHW.realEmbed x (ρ k)))
      =
    BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed (fun k => x (τ k))) -
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  simpa [Pid, Pswap] using
    BHW.os45PulledRealBranch_sub_eq_adjacentOS45RealEdgeDifference
      (d := d) (n := n) OS lgc τ ρ x
```

Lean-ready common-chart supplier and checked direct-envelope transcript:

```lean
let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
rcases BHW.os45_adjacent_localEOWGeometry
    (d := d) (n := n) hd i hi with
  ⟨V, ρ, hV_open, hV_conn, hV_ne, hV_jost, hV_ET, hV_swapET,
    hV_ordered, hV_swap_ordered, hV_wick, hV_real,
    hV_geom, hV_swap_geom⟩

-- The genuine OS45 common-boundary theorem, proved from the two
-- `OS45OppositeTubeBranchGeometry` packets and the OS-II/ACR-one Wick branch
-- data, must return a common chart and not merely a domain.
have hCommon :
    ∃ (Uc : Set (Fin n -> Fin (d + 1) -> ℂ))
      (Hc : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ),
      IsOpen Uc ∧ IsConnected Uc ∧
      DifferentiableOn ℂ Hc Uc ∧
      (∀ x ∈ V,
        BHW.os45CommonChartCLE (d := d) (n := n) ρ
          (fun k => wickRotatePoint (x k)) ∈ Uc) ∧
      (∀ x ∈ V,
        BHW.os45CommonChartCLE (d := d) (n := n) ρ
          (BHW.realEmbed (d := d) x) ∈ Uc) ∧
      (∀ x ∈ V,
        Hc (BHW.os45CommonChartCLE (d := d) (n := n) ρ
            (fun k => wickRotatePoint (x k))) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
      (∀ x ∈ V,
        Hc (BHW.os45CommonChartCLE (d := d) (n := n) ρ
            (BHW.realEmbed (d := d) x)) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (d := d) (fun k => x (τ k))) -
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (d := d) x)) := by
  exact
    BHW.os45_adjacent_commonBoundaryEnvelope
      (d := d) hd OS lgc n i hi V ρ
      hV_open hV_conn hV_ne hV_jost hV_ET hV_swapET
      hV_ordered hV_swap_ordered hV_wick hV_real
      hV_geom hV_swap_geom

rcases hCommon with
  ⟨Uc, Hc, hUc_open, hUc_conn, hHc_holo,
    hwick_mem_c, hreal_mem_c, hwick_trace_c, hreal_trace_c⟩

exact
  BHW.adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope
    (d := d) OS lgc n i hi V ρ Uc Hc
    hUc_open hUc_conn hHc_holo
    hwick_mem_c hreal_mem_c hwick_trace_c hreal_trace_c
```

The new theorem named in this transcript,
`BHW.os45_adjacent_commonBoundaryEnvelope`, is not a wrapper: it is the exact
OS45 common-boundary / EOW step.  Its proof obligations are the real
mathematical content:

1. construct the common OS45 chart domain from the two
   `OS45OppositeTubeBranchGeometry` packets over the same `V`;
2. identify the positive-side trace with the adjacent `bvt_F` Wick difference;
3. identify the negative-side trace with the adjacent `extendF` real-edge
   difference using
   `BHW.os45PulledRealBranch_sub_eq_adjacentOS45RealEdgeDifference`;
4. export connectedness of the one common chart domain used by both traces.

The coordinate infrastructure needed by this transcript is now implemented in
`Wightman/Reconstruction/WickRotation/OSToWightmanLocalityOS45CommonChart.lean`.
It supplies the complex-linear chart equivalence

```lean
#check BHW.configPermCLE
#check BHW.configPermCLE_apply
#check BHW.configPermCLE_symm_apply

#check BHW.os45CommonChartCLE
#check BHW.os45CommonChartCLE_apply
#check BHW.os45CommonChartCLE_symm_apply
```

Their defining equations are:

```lean
BHW.configPermCLE (d := d) (n := n) ρ z =
  fun k μ => z (ρ k) μ

(BHW.configPermCLE (d := d) (n := n) ρ).symm z =
  fun k μ => z (ρ.symm k) μ

BHW.os45CommonChartCLE (d := d) (n := n) ρ z =
  BHW.os45QuarterTurnConfig (d := d) (n := n) (fun k μ => z (ρ k) μ)
```

The implemented definitions have the surfaces:

```lean
noncomputable def configPermCLE
    (ρ : Equiv.Perm (Fin n)) :
    (Fin n -> Fin (d + 1) -> ℂ) ≃L[ℂ]
      (Fin n -> Fin (d + 1) -> ℂ)

noncomputable def os45CommonChartCLE
    (ρ : Equiv.Perm (Fin n)) :
    (Fin n -> Fin (d + 1) -> ℂ) ≃L[ℂ]
      (Fin n -> Fin (d + 1) -> ℂ)
```

This is coordinate bookkeeping, but it is not a theorem-2 replacement theorem:
it exists only so the common-chart EOW output can be pulled back to the direct
coordinates required by `AdjacentOSEOWDifferenceEnvelope`.

Internal transcript for `BHW.os45_adjacent_commonBoundaryEnvelope`:

```lean
theorem BHW.os45_adjacent_commonBoundaryEnvelope
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n))
    (hV_open : IsOpen V) (hV_conn : IsConnected V) (hV_ne : V.Nonempty)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_swapET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
    (hV_ordered :
      ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (hV_swap_ordered :
      ∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
    (hV_wick :
      ∀ x ∈ V,
        (fun k => wickRotatePoint (x k)) ∈
          adjacentOS45WickSeedDomain (d := d) (n := n) i hi ρ)
    (hV_real :
      ∀ x ∈ V,
        BHW.realEmbed x ∈
          adjacentOS45RealEdgeDomain (d := d) (n := n) i hi)
    (hV_geom :
      ∀ x ∈ V, BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n) ρ x)
    (hV_swap_geom :
      ∀ x ∈ V,
        BHW.OS45OppositeTubeBranchGeometry (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    ∃ (Uc : Set (Fin n -> Fin (d + 1) -> ℂ))
      (Hc : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ),
      IsOpen Uc ∧ IsConnected Uc ∧
      DifferentiableOn ℂ Hc Uc ∧
      (∀ x ∈ V,
        BHW.os45CommonChartCLE (d := d) (n := n) ρ
          (fun k => wickRotatePoint (x k)) ∈ Uc) ∧
      (∀ x ∈ V,
        BHW.os45CommonChartCLE (d := d) (n := n) ρ
          (BHW.realEmbed (d := d) x) ∈ Uc) ∧
      (∀ x ∈ V,
        Hc (BHW.os45CommonChartCLE (d := d) (n := n) ρ
            (fun k => wickRotatePoint (x k))) =
          bvt_F OS lgc n
            (fun k => wickRotatePoint (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
          bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
      (∀ x ∈ V,
        Hc (BHW.os45CommonChartCLE (d := d) (n := n) ρ
            (BHW.realEmbed (d := d) x)) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (d := d)
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (d := d) x))
```

Implementation-readiness audit for this packet:

* The pure distributional EOW/uniqueness infrastructure is not the live
  mathematical blocker.  The theorem above is the theorem-2-specific OS45
  instantiation: it must put the already available common-boundary/EOW
  machinery into the fixed common chart and export the concrete trace
  identities consumed by
  `BHW.adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope`.
* The checked production inputs are
  `BHW.os45_adjacent_localEOWGeometry`,
  `BHW.adjacent_wick_traces_mem_acrOne`,
  `BHW.os45CommonChart_real_mem_pulledRealBranchDomain_pair`,
  `BHW.os45PulledRealBranch_holomorphicOn`,
  `BHW.os45PulledRealBranch_sub_eq_adjacentOS45RealEdgeDifference`, and
  `BHW.adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope`.
* The missing theorem is the common-chart envelope constructor itself:
  `BHW.os45_adjacent_commonBoundaryEnvelope`.  If an auxiliary SCV-local
  envelope theorem is introduced, it must be QFT-free and must feed this
  concrete OS45 envelope; it is not a new assumption and not a replacement for
  `SelectedAdjacentDistributionalJostAnchorData`.
* Once this theorem is checked, `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII`
  is field-by-field bookkeeping plus the checked Gram-environment supplier
  `BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch`;
  the already checked projection `bvt_F_distributionalJostAnchor_of_selectedJostData`
  then supplies `BHW.SourceDistributionalAdjacentTubeAnchor`.

Proof decomposition of this theorem, without hiding the analytic work:

1. Set `τ := Equiv.swap i ⟨i.val + 1, hi⟩` and
   `Qρe := BHW.os45CommonChartCLE (d := d) (n := n) ρ`.
2. Define the positive-side branch difference on the pulled OS-II ACR-one
   wedge.  The domain must be written in ordered coordinates; otherwise the
   theorem would silently assume that the selected patch is identity-ordered.
   The trace value is still the direct adjacent difference, because
   `bvt_F_acrOne_package` supplies total permutation symmetry.

   ```lean
   let Dplus : Set (Fin n -> Fin (d + 1) -> ℂ) :=
     {z |
       BHW.permAct (d := d) ρ (Qρe.symm z) ∈
         AnalyticContinuationRegion d n 1 ∧
       BHW.permAct (d := d) (τ.symm * ρ)
         (BHW.permAct (d := d) τ (Qρe.symm z)) ∈
         AnalyticContinuationRegion d n 1}

   let Hplus : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ := fun z =>
     bvt_F OS lgc n (BHW.permAct (d := d) τ (Qρe.symm z)) -
       bvt_F OS lgc n (Qρe.symm z)
   ```

   The proof of `DifferentiableOn ℂ Hplus Dplus` uses
   `(bvt_F_acrOne_package (d := d) OS lgc n).1` after rewriting each direct
   `bvt_F` term by the permutation-symmetry field
   `(bvt_F_acrOne_package (d := d) OS lgc n).2.2.1`; the two ACR-one
   memberships are exactly the two ordered-sector hypotheses.  The required
   coordinate maps are differentiable because they are finite coordinate
   permutations composed with `Qρe.symm`.

   The ordered-sector to ACR-one bridge is also implemented in
   `OSToWightmanLocalityOS45CommonChart.lean`:

   ```lean
   theorem BHW.wickRotate_ordered_mem_acrOne
       [NeZero d]
       (σ : Equiv.Perm (Fin n))
       {x : NPointDomain d n}
       (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) σ) :
       BHW.permAct (d := d) σ (fun k => wickRotatePoint (x k)) ∈
         AnalyticContinuationRegion d n 1
   ```

   This is a direct calculation from the definition of
   `AnalyticContinuationRegion d n 1` and the strict positive ordered-time
   inequalities; it is coordinate mathematics, not a theorem-2 wrapper.
3. Define the negative-side branch difference using the checked real pullbacks:

   ```lean
   let Dminus : Set (Fin n -> Fin (d + 1) -> ℂ) :=
     BHW.os45PulledRealBranchDomain (d := d) (n := n) ρ ∩
       BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ)

   let Hminus : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ := fun z =>
     BHW.os45PulledRealBranch (d := d) (n := n) OS lgc (τ.symm * ρ) z -
       BHW.os45PulledRealBranch (d := d) (n := n) OS lgc ρ z
   ```

   `DifferentiableOn ℂ Hminus Dminus` is exactly
   `os45PulledRealBranch_holomorphicOn` on each factor, restricted to the
   intersection.
4. The two trace memberships are not optional side facts.  They are proved from
   the two ordered-sector hypotheses and the two
   `OS45OppositeTubeBranchGeometry` packets:

   ```lean
   have hplus_trace_mem :
       ∀ x ∈ V, Qρe (fun k => wickRotatePoint (x k)) ∈ Dplus := by
     intro x hx
     simpa [Dplus, Qρe, τ] using
       BHW.adjacent_wick_traces_mem_acrOne
         (d := d) (n := n) i hi ρ
         (hV_ordered x hx) (hV_swap_ordered x hx)

   have hminus_trace_mem :
       ∀ x ∈ V, Qρe (BHW.realEmbed (d := d) x) ∈ Dminus := by
     intro x hx
     simpa [Dminus, Qρe, τ] using
       BHW.os45CommonChart_real_mem_pulledRealBranchDomain_pair
         (d := d) (n := n) τ ρ (hV_ET x hx) (hV_swapET x hx)
   ```

5. Do **not** introduce placeholder boundary predicates.  The current repo
   APIs are exact and must be used by name:

   - `SCV.edge_of_the_wedge_theorem` in
     `SCV/TubeDomainExtension.lean` constructs an envelope from **continuous
     pointwise** boundary values on an open real edge.
   - `SCV.distributional_uniqueness_tube_of_zero_bv` and
     `SCV.distributional_uniqueness_tube_of_zero_bv_of_clm` in
     `SCV/DistributionalUniqueness.lean` prove zero/uniqueness from
     **distributional** boundary values.
   - `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` in
     `OSToWightmanTubeIdentity.lean` is already the checked local consumer that
     turns compact-test Wick-section equality on a real-open patch into
     pointwise equality on a connected holomorphic chart.

   Hence Slot 1 must not add a structure named
   `HasCommonDistributionalBoundaryValueOn`, a symbolic
   `BoundaryPairingLimit`, or any similar field package.  If the implementation
   uses continuous EOW, it must first prove the actual continuous `bv`,
   `ContinuousOn bv E`, and the two pointwise `Tendsto` hypotheses required by
   `SCV.edge_of_the_wedge_theorem`.  If the implementation stays in the OS-II
   distributional category, it must state and prove a genuine local
   distributional EOW envelope theorem, not assume one through a record field.

   The continuous-EOW extraction needed inside the distributional proof should
   itself have a uniform geometric theorem surface, because the regularized
   family must use one fixed chart domain `U0` for every smoothing kernel.  The
   Lean target is:

   ```lean
   theorem SCV.local_continuous_edge_of_the_wedge_geometry
       {m : ℕ}
       (Ωplus Ωminus : Set (ComplexChartSpace m))
       (E : Set (Fin m -> ℝ))
       (hΩplus_open : IsOpen Ωplus)
       (hΩminus_open : IsOpen Ωminus)
       (hE_open : IsOpen E)
       (hE_ne : E.Nonempty)
       (C : Set (Fin m -> ℝ))
       (hC_open : IsOpen C)
       (hC_conv : Convex ℝ C)
       (hC_ne : C.Nonempty)
       (hC_not_zero : (0 : Fin m -> ℝ) ∉ C)
       (hC_cone : ∀ (t : ℝ), 0 < t -> ∀ y ∈ C, t • y ∈ C)
       (hlocal_wedge :
         ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ E ->
           ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
             ∃ r : ℝ, 0 < r ∧
               ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
                 (fun a => (x a : ℂ) +
                   (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
                 (fun a => (x a : ℂ) -
                   (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus) :
       ∃ U0 : Set (ComplexChartSpace m),
         IsOpen U0 ∧
         (∀ x ∈ E, realEmbed x ∈ U0) ∧
         ∀ (Fplus Fminus : ComplexChartSpace m -> ℂ)
           (bv : (Fin m -> ℝ) -> ℂ),
           DifferentiableOn ℂ Fplus Ωplus ->
           DifferentiableOn ℂ Fminus Ωminus ->
           ContinuousOn bv E ->
           (∀ x ∈ E,
             Tendsto Fplus (nhdsWithin (realEmbed x) Ωplus)
               (nhds (bv x))) ->
           (∀ x ∈ E,
             Tendsto Fminus (nhdsWithin (realEmbed x) Ωminus)
               (nhds (bv x))) ->
             ∃ F : ComplexChartSpace m -> ℂ,
               DifferentiableOn ℂ F U0 ∧
               (∀ z ∈ U0 ∩ Ωplus, F z = Fplus z) ∧
               (∀ z ∈ U0 ∩ Ωminus, F z = Fminus z) ∧
               (∀ G : ComplexChartSpace m -> ℂ,
                 DifferentiableOn ℂ G U0 ->
                 (∀ z ∈ U0 ∩ Ωplus, G z = Fplus z) ->
                 (∀ z ∈ U0 ∩ Ωminus, G z = Fminus z) ->
                   ∀ z ∈ U0, G z = F z)
   ```

   Side-component discipline for this continuous layer: the local wedge
   hypothesis supplies explicit small plus/minus chart wedges inside
   `Ωplus/Ωminus`; it does not by itself rule out arbitrary extra open
   components of `Ωplus/Ωminus` accumulating near the edge.  The implementation
   must therefore prove agreement first on those explicit side domains (the
   checked helpers are
   `SCV.localEOWChart_ball_positive_mem_of_delta` and
   `SCV.localEOWChart_ball_negative_mem_of_delta`) and only enlarge an
   agreement statement to `U0 ∩ Ωplus` or `U0 ∩ Ωminus` when an explicit
   side-connectedness/connected-component hypothesis is available.  The OS45
   consumer gets that connected common chart later from the BHW layer; the pure
   SCV regularization route only needs agreement on the constructed side
   wedges.

   Proof transcript:

   1. choose for each `x0 ∈ E` a local polybox using `hlocal_wedge`, exactly as
      `SCV.edge_of_the_wedge_theorem` chooses its polydiscs from the global
      tube geometry;
   2. define `U0` as the union of these boxes before any functions are supplied;
   3. for fixed `Fplus,Fminus,bv`, run the existing Cauchy-polydisc extension
      construction on each box, replacing the global `TubeDomain C` membership
      lemmas by the local wedge membership supplied in step 1;
   4. patch the local continuous envelopes by the ordinary identity theorem on
      the plus or minus wedge pieces;
   5. prove uniqueness on `U0` by the same identity-theorem argument, using that
      each component of `U0` meets one of the local wedge pieces.

6. The theorem surface needed by Slot 1 is therefore the following pure-SCV
   local chart-envelope adapter, followed by its OS45 instantiation.  This
   theorem packages the existing distributional edge-of-the-wedge machinery
   into the local chart data used by OS §4.5.  It is not a new axiom, not a
   replacement for the checked distributional EOW infrastructure, and it must
   not mention OS, Wightman functions, `bvt_F`, `extendF`, or locality.

   ```lean
   theorem SCV.local_distributional_edge_of_the_wedge_envelope
       {m : ℕ}
       (Ωplus Ωminus : Set (Fin m -> ℂ))
       (E : Set (Fin m -> ℝ))
       (hΩplus_open : IsOpen Ωplus)
       (hΩminus_open : IsOpen Ωminus)
       (hE_open : IsOpen E)
       (hE_ne : E.Nonempty)
       (C : Set (Fin m -> ℝ))
       (hC_open : IsOpen C)
       (hC_conv : Convex ℝ C)
       (hC_ne : C.Nonempty)
       (hC_not_zero : (0 : Fin m -> ℝ) ∉ C)
       (hC_cone : ∀ (t : ℝ), 0 < t -> ∀ y ∈ C, t • y ∈ C)
       -- `Kη` represents a compact set of directions in a closed subcone
       -- compactly contained in `C`.  This is the Lean-facing substitute for
       -- the usual `C₀ ⋐ C` notation.
       (hlocal_wedge :
         ∀ K : Set (Fin m -> ℝ), IsCompact K -> K ⊆ E ->
           ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
             ∃ r : ℝ, 0 < r ∧
               ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
                 (fun a => (x a : ℂ) +
                   (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
                 (fun a => (x a : ℂ) -
                   (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
       (Fplus Fminus : (Fin m -> ℂ) -> ℂ)
       (hFplus : DifferentiableOn ℂ Fplus Ωplus)
       (hFminus : DifferentiableOn ℂ Fminus Ωminus)
       (T : SchwartzMap (Fin m -> ℝ) ℂ ->L[ℂ] ℂ)
       -- In this repo, `SchwartzMap` plus compact support and support inside
       -- `E` is the current Lean representation of `C_c^∞(E)`.
       (hplus_bv :
         ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
           ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
             HasCompactSupport (φ : (Fin m -> ℝ) -> ℂ) ->
             tsupport (φ : (Fin m -> ℝ) -> ℂ) ⊆ E ->
             TendstoUniformlyOn
               (fun ε η =>
                 ∫ x : Fin m -> ℝ,
                   Fplus (fun a => (x a : ℂ) +
                     (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
               (fun _ : Fin m -> ℝ => T φ)
               (nhdsWithin 0 (Set.Ioi 0))
               Kη)
       (hminus_bv :
         ∀ Kη : Set (Fin m -> ℝ), IsCompact Kη -> Kη ⊆ C ->
           ∀ φ : SchwartzMap (Fin m -> ℝ) ℂ,
             HasCompactSupport (φ : (Fin m -> ℝ) -> ℂ) ->
             tsupport (φ : (Fin m -> ℝ) -> ℂ) ⊆ E ->
             TendstoUniformlyOn
               (fun ε η =>
                 ∫ x : Fin m -> ℝ,
                   Fminus (fun a => (x a : ℂ) -
                     (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
               (fun _ : Fin m -> ℝ => T φ)
               (nhdsWithin 0 (Set.Ioi 0))
               Kη) :
       ∃ (U Uplus Uminus : Set (Fin m -> ℂ))
         (F : (Fin m -> ℂ) -> ℂ),
         IsOpen U ∧
         IsOpen Uplus ∧
         IsOpen Uminus ∧
         Uplus ⊆ U ∩ Ωplus ∧
         Uminus ⊆ U ∩ Ωminus ∧
         (∀ x ∈ E, realEmbed x ∈ U) ∧
         -- Every connected component of the constructed envelope domain meets
         -- one of the explicit side windows.  This is the Lean-facing
         -- uniqueness seed; the theorem does not claim agreement on arbitrary
         -- extra components of `U ∩ Ωplus` or `U ∩ Ωminus`.
         (∀ z ∈ U, ∃ V : Set (Fin m -> ℂ),
           IsOpen V ∧ IsPreconnected V ∧ z ∈ V ∧ V ⊆ U ∧
             ((V ∩ Uplus).Nonempty ∨ (V ∩ Uminus).Nonempty)) ∧
         DifferentiableOn ℂ F U ∧
         (∀ z ∈ Uplus, F z = Fplus z) ∧
         (∀ z ∈ Uminus, F z = Fminus z) ∧
         (∀ G : (Fin m -> ℂ) -> ℂ,
           DifferentiableOn ℂ G U ->
           (∀ z ∈ Uplus, G z = Fplus z) ->
           (∀ z ∈ Uminus, G z = Fminus z) ->
             ∀ z ∈ U, G z = F z)
   ```

   The side-agreement clauses intentionally use explicit side windows
   `Uplus,Uminus`, not all of `U ∩ Ωplus` and `U ∩ Ωminus`.  The local
   continuous EOW construction only proves agreement on the constructed
   positive/negative wedge pieces unless an additional side-connectedness
   theorem is supplied.  The final uniqueness clause is still strong enough:
   every connected patch of `U` is seeded by one of those explicit side
   windows, so the ordinary identity theorem propagates equality across the
   constructed envelope domain without making a false claim about unrelated
   components of the ambient wedge sets.

   Implementation-readiness correction for the final SCV theorem:

   * The theorem statement intentionally has no explicit `hm : 0 < m`.  Lean
     must derive it internally from `hC_ne` and `hC_not_zero` using
     `SCV.positive_dimension_of_nonempty_not_zero`: if `m = 0`, every vector
     `Fin 0 -> ℝ` is zero, contradicting `C.Nonempty` and `0 ∉ C`.
   * Choose the cone basis `ys` **once globally** after deriving `hm`, and use
     that same `ys` for every local edge point.  Patching cannot use unrelated
     per-point bases: two local patches then need not have a common positive
     side window on their overlap.  With one fixed basis, overlaps of
     transported chart balls have a real point by conjugation/convexity, and a
     small common positive-coordinate displacement seeds the identity theorem.
   * The single-point checked helper
     `SCV.exists_localContinuousEOW_chart_window` remains useful as a source
     pattern, but the final proof should introduce the fixed-basis variant
     `SCV.exists_localContinuousEOW_fixedBasis_chart_window`, whose proof is
     the checked body after the `open_set_contains_basis` line:
     `localEOWRealChart_closedBall_subset`,
     `localEOWChart_twoSided_polywedge_mem`, and
     `exists_localEOWSmp_delta`.
   * The coordinate envelope returned by local descent must be transported
     back through a complex affine chart equivalence
     `SCV.localEOWComplexAffineEquiv x0 ys hli`.  The checked real-linear
     kernel pushforward fixes the mollifier variables; it does not by itself
     prove that `z ↦ Hcoord (A.symm z)` is holomorphic on an open original
     chart image.
   * Patching must go through the named fixed-basis overlap package:
     `SCV.localEOWFixedBasis_overlap_positiveSeed`,
     `SCV.distributionalEOW_extensions_compatible`, and
     `SCV.localDistributionalEOW_patch_extensions`.  The patch theorem is also
     where the final real-edge cover, side-window component seed, and
     uniqueness clause are assembled.

   Proof-doc readiness gate for this SCV theorem:

   * The final theorem may enter Lean only after the one-chart theorem surface
     has no hidden hypothesis comments.  The one-chart proof-doc surface is now:
     `SCV.HasCompactSupport.localEOWAffineTestPushforwardCLM`,
     `SCV.tsupport_localEOWAffineTestPushforwardCLM_subset`,
     `SCV.localEOWAffineTestPushforwardCLM_apply_realChart`,
     `SCV.integral_localEOWAffineTestPushforwardCLM_changeOfVariables`,
     `SCV.localEOW_basisSideCone_rawBoundaryValue`,
     `SCV.exists_localEOW_truncatedSideCones_for_sliceMargin`,
     `SCV.exists_localEOWRealLinearPart_ball_subset`,
     `SCV.StrictPositiveImagBall`,
     `SCV.StrictNegativeImagBall`,
     `SCV.StrictPositiveImagBall_add_realEmbed_mem_ball_of_norm_le`,
     `SCV.StrictNegativeImagBall_add_realEmbed_mem_ball_of_norm_le`,
     `SCV.isOpen_StrictPositiveImagBall`,
     `SCV.isOpen_StrictNegativeImagBall`,
     `SCV.StrictPositiveImagBall_im_nonneg`,
     `SCV.StrictNegativeImagBall_im_nonpos`,
     `SCV.StrictPositiveImagBall_im_sum_pos`,
     `SCV.StrictNegativeImagBall_neg_im_sum_pos`,
     `SCV.StrictPositiveImagBall_im_sum_le_card_mul`,
     `SCV.StrictNegativeImagBall_neg_im_sum_le_card_mul`,
     `SCV.localEOWChart_im_eq_realLinearPart_im`,
     `SCV.localEOWChart_mem_TubeDomain_truncatedSideCone_of_strictPositive`,
     `SCV.localEOWChart_mem_TubeDomain_neg_truncatedSideCone_of_strictNegative`,
     `SCV.localEOWChart_mem_fixedWindow_of_strictPositiveImagBall`,
     `SCV.localEOWChart_mem_fixedWindow_of_strictNegativeImagBall`,
     `SCV.KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_of_le_four_mul`,
     `SCV.exists_oneChartRecoveryScale`,
     `SCV.oneChartRecoveryScale_radius_margins`,
     `SCV.oneChartRecoveryScale_core_translate_mem_desc`,
     `SCV.oneChartRecoveryScale_desc_translate_mem_cov`,
     `SCV.oneChartRecoveryScale_cov_ball_subset_half`,
     `SCV.oneChartRecoveryScale_cut_closedBall_subset_half`,
     `SCV.localEOWAffineRealWindow`,
     `SCV.isOpen_localEOWAffineRealWindow`,
     `SCV.localEOWComplexAffineEquiv_symm_localEOWChart`,
     `SCV.localEOWAffineRealWindow_add_realEmbed`,
     `SCV.localEOWComplexAffineEquiv_symm_add_realEmbed`,
     `SCV.exists_localEOWRealLinearSymm_ball_subset`,
     `SCV.tendstoUniformlyOn_const_comp_of_tendsto_of_eventually_mem`,
     `SCV.coordSum_tendsto_positiveOrthant_nhdsWithin_Ioi`,
     `SCV.coordNegSum_tendsto_negativeOrthant_nhdsWithin_Ioi`,
     `SCV.localEOWChart_real_add_imag`,
     `SCV.chartOrthantBoundaryValue_from_uniformConeBoundaryValue`,
     `SCV.chartHolomorphy_from_originalHolomorphy`,
     `SCV.exists_schwartz_cutoff_eq_one_on_closedBall`,
     `SCV.exists_complexChart_schwartz_cutoff_eq_one_on_closedBall`,
     `SCV.exists_cutoffSliceCLM_family_of_boundaryValue_of_cutoffSupport`,
     `SCV.sliceCLM_family_from_distributionalBoundary_of_cutoffSupport`,
     `SCV.regularizedLocalEOW_family_from_fixedWindow`,
     `SCV.regularizedLocalEOW_originalFamily_compactValueCLM`,
     `SCV.regularizedLocalEOW_chartKernelFamily_valueCLM`,
     `SCV.continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand`,
     `SCV.regularizedLocalEOW_pairingCLM_of_fixedWindow`,
     `SCV.regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap`,
     `SCV.regularizedLocalEOW_chartKernelFamily_outputs_from_fixedWindow`,
     `SCV.chartSideFunction_continuousOn_strictBalls_from_fixedWindow`,
     `SCV.localEOWPreparedSideDomains_from_fixedWindow`,
     `SCV.localEOWAffineTestPushforwardCLM_apply_re`,
     `SCV.localEOWAffineCutoff_one_of_affineRealWindow_add`,
     `SCV.localEOWAffineCutoff_one_on_translatedKernel`,
     `SCV.localEOWSliceCLMs_from_preparedDomains`,
     `SCV.regularizedLocalEOW_pairingCLM_localCovariant`,
     `SCV.regularizedLocalEOW_pairingCLM_localCovariant_from_fixedWindow`,
     `SCV.exists_normalized_schwartz_bump_kernelSupportWithin`,
     `SCV.exists_shrinking_normalized_schwartz_bump_sequence`,
     `SCV.tendsto_realConvolutionTest_of_shrinking_normalized_support`,
     `SCV.StrictPositiveImagBall_mono`,
     `SCV.StrictNegativeImagBall_mono`,
     `SCV.tendsto_realMollifyLocal_strictPositiveImagBall`,
     `SCV.tendsto_realMollifyLocal_strictNegativeImagBall`,
     `SCV.regularizedEnvelope_chartEnvelope_from_oneChartScale`,
     `SCV.regularizedLocalEOW_chartEnvelope_from_fixedWindowScale`,
     `SCV.chartDistributionalEOW_local_envelope`,
     `SCV.chartDistributionalEOW_transport_originalCoords`,
     `SCV.localEOWChart_change_basepoint`,
     `SCV.localEOWComplexAffineEquiv_sameBasis_transition`,
     `SCV.localEOWFixedBasisCoordinateOverlap`,
     `SCV.isOpen_localEOWFixedBasisCoordinateOverlap`,
     `SCV.convex_localEOWFixedBasisCoordinateOverlap`,
     `SCV.localEOWFixedBasis_coordinateOverlap_real_seed`,
     `SCV.localEOWFixedBasis_coordinateOverlap_positiveSeed`,
     `SCV.localEOWFixedBasis_overlap_positiveSeed`,
     `SCV.distributionalEOW_extensions_compatible`, and
     `SCV.localDistributionalEOW_patch_extensions`.
     `SCV.chartSlowGrowth_from_uniformConeSlowGrowth` remains documented as an
     outer OS-II boundary-value construction tool, but it is not a formal
     argument of `SCV.chartDistributionalEOW_local_envelope` once
     `hplus_bv` and `hminus_bv` are supplied.
   * `SCV.chartOrthantBoundaryValue_from_uniformConeBoundaryValue` is the
     checked sign/Jacobian theorem.  Positive chart directions use
     `s = ∑ j, y j` and
     `η = s⁻¹ • localEOWRealLinearPart ys y`; negative chart directions use
     `s = ∑ j, -y j` and
     `η = s⁻¹ • localEOWRealLinearPart ys (-y)`.  The latter gives
     `localEOWRealLinearPart ys y = -s • η`, so it consumes exactly the final
     `Fminus (x - εη i)` hypothesis.  The proof uses uniform convergence on
     `localEOWSimplexDirections ys` through the generic helper
     `tendstoUniformlyOn_const_comp_of_tendsto_of_eventually_mem`; this is
     important because the normalized direction may vary with `y` and has no
     single limit.  The coordinate sums tend to `0` within `Set.Ioi 0` by
     `coordSum_tendsto_positiveOrthant_nhdsWithin_Ioi` and
     `coordNegSum_tendsto_negativeOrthant_nhdsWithin_Ioi`, and
     `localEOWChart_real_add_imag` performs the final chart-to-original
     imaginary-coordinate rewrite.
   * The distribution in chart coordinates is not `T`; it is
     `localEOWAffineDistributionPullbackCLM x0 ys hli T`, and the smoothing
     kernels used in the regularized family are pushed to the original edge by
     `localEOWRealLinearKernelPushforwardCLM ys hli`.
   * The affine support half of this gate is checked:
     `HasCompactSupport.localEOWAffineTestPushforwardCLM` and
     `tsupport_localEOWAffineTestPushforwardCLM_subset`.  The determinant
     theorem is also checked as
     `SCV.integral_localEOWAffineTestPushforwardCLM_changeOfVariables`:
     evaluate the pushed test on `localEOWRealChart x0 ys u` to get `φ u`,
     then apply the finite-dimensional affine change-of-variables theorem.
     Holomorphy transport through `localEOWChart` is checked as
     `SCV.chartHolomorphy_from_originalHolomorphy`.
   * The local output must be a transported coordinate ball with transported
     strict positive/negative side balls.  Patching consumes precisely these
     shapes:
     `(localEOWComplexAffineEquiv x0 ys hli) '' Metric.ball 0 R`,
     `(localEOWComplexAffineEquiv x0 ys hli) '' StrictPositiveImagBall R`,
     and
     `(localEOWComplexAffineEquiv x0 ys hli) '' StrictNegativeImagBall R`.
     For two patches with the same basis `ys`, their overlap is pulled back to
     the first chart as
     `Metric.ball 0 R₁ ∩ {w | w - realEmbed d ∈ Metric.ball 0 R₂}`,
     where `d = (localEOWRealLinearCLE ys hli).symm (x₂ - x₁)`.  The
     transition formula
     `(localEOWComplexAffineEquiv x₂ ys hli).symm
       ((localEOWComplexAffineEquiv x₁ ys hli) w) = w - realEmbed d`
     is the exact sign convention for this shift.  Openness, convexity,
     conjugation invariance, the real seed, and the small positive-imaginary
     displacement are all named helper lemmas before the compatibility theorem.
   * The patching proof constructs
     `U = ⋃ i, Uloc i`, `Uplus = ⋃ i, UplusLoc i`,
     `Uminus = ⋃ i, UminusLoc i`, and defines the total function
     `H z = if hz : ∃ i, z ∈ Uloc i then Hloc (Classical.choose hz) z else 0`.
     Compatibility proves the local rewrite `H z = Hloc i z` for every
     explicit witness `z ∈ Uloc i`; holomorphy and side identities are then
     local on that patch.  Well-definedness is exactly
     `distributionalEOW_extensions_compatible`; uniqueness is exactly the
     side-seeded identity theorem packaged in
     `localDistributionalEOW_patch_extensions`.
   * The final SCV assembly uses `ι = {x : Fin m -> ℝ // x ∈ E}`.  For each
     `i : ι`, call `SCV.chartDistributionalEOW_local_envelope` with the single
     global basis `ys`, then call
     `SCV.chartDistributionalEOW_transport_originalCoords` and store the
     transported patch as `Uloc i`, `UplusLoc i`, `UminusLoc i`, `Hloc i`.
     The real-edge cover is the transported fact `realEmbed i.1 ∈ Uloc i`.
     The patch theorem's seed hypothesis is supplied by `V = Uloc i`, using
     the transport outputs `IsOpen (Uloc i)`, `IsPreconnected (Uloc i)`, and
     `UplusLoc i.Nonempty` (or the negative companion).  Pairwise
     compatibility on overlaps is exactly
     `SCV.distributionalEOW_extensions_compatible`.

   Proof transcript for the SCV theorem:

   1. Derive `hm : 0 < m` from `hC_ne` and `hC_not_zero`.  Then choose a
      single global basis `ys : Fin m -> Fin m -> ℝ` with
      `∀ j, ys j ∈ C` and `LinearIndependent ℝ ys` by the checked
      `SCV.open_set_contains_basis hm C hC_open hC_ne`.  Keep `ys` fixed for
      every chart in the rest of the proof; do not introduce a production
      wrapper just to rename this existing theorem.
   2. For each compact real set `K ⊆ E` and compact direction set `Kη ⊆ C`,
      use `hlocal_wedge` to get a radius `r > 0` so the truncated wedges
      `x ± i εη`, `x ∈ K`, `η ∈ Kη`, `0 < ε < r`, lie in `Ωplus/Ωminus`.
      This is the local replacement for a global tube hypothesis.
   3. The OS-II slow-growth estimates are verified in the outer construction
      of the distributional boundary values, not as assumptions of the
      one-chart SCV envelope.  Once the Lean hypotheses `hplus_bv` and
      `hminus_bv` below are supplied, no slow-growth argument is used in
      `SCV.chartDistributionalEOW_local_envelope`.
   4. Use `hplus_bv` and `hminus_bv` as uniform compact-subcone boundary
      convergence statements.  In the current Lean surface, compactly supported
      `SchwartzMap`s with `tsupport ⊆ E` represent the local test space
      `C_c^\infty(E)`.
   5. First prove the pure-SCV local **continuous** EOW theorem
      `SCV.local_continuous_edge_of_the_wedge_envelope`.  This is not a
      wrapper around the checked global `SCV.edge_of_the_wedge_theorem`, because
      that theorem is stated for global tubes.  The proof must extract the
      Cauchy-polydisc construction from `SCV/TubeDomainExtension.lean` and
      replace `Phi_pos_in_tube` / `Phi_neg_in_tube` by local compact-subcone
      membership lemmas using `hlocal_wedge`.
   6. Use the **Streater-Wightman distributional EOW route** from Theorem
      2-16 of the Wightman book: real-direction convolution regularization,
      continuous EOW for each compactly supported smoothing kernel, kernel
      extraction by the Schwartz nuclear theorem, translation covariance, and
      compactly supported approximate-identity recovery.  The rejected
      finite-order primitive route is not active: in several variables
      separately normalized holomorphic primitives can differ by arbitrary
      transverse holomorphic functions, and the naive polynomial-correction
      shortcut is false.
   7. At a real edge point `x0 ∈ E`, use the already fixed cone-basis vectors
      `ys : Fin m -> Fin m -> ℝ` with `ys j ∈ C`; the distribution pullback
      needs the real affine chart and its linear part
      `localEOWRealLinearPart ys`, while the immediate
      neighborhood-containment step only uses continuity of
      `localEOWRealChart x0 ys`.  The checked local target is
      `SCV.localEOWRealChart_closedBall_subset`: choose `ρ > 0` with
      `Metric.closedBall 0 ρ` mapped into `E`.  The positive and negative chart
      polywedges over the inner ball are then fed to
      `SCV.localEOWChart_twoSided_polywedge_mem`.
   8. Pull `Fplus`, `Fminus`, and the common distribution `T` through this
      chart only at the points where a chart-coordinate object is actually
      needed.  The affine distribution pullback includes the
      determinant/Jacobian factor of the real linear chart, and the real
      smoothing kernels are transported by
      `SCV.localEOWRealLinearKernelPushforwardCLM`.  The boundary-value input
      for the one-chart theorem is obtained by
      `SCV.localEOW_basisSideCone_rawBoundaryValue`: first shrink the compact
      direction simplex to an open side cone whose closed direction envelope
      lies in `C ∩ {η | η ≠ 0}`, then restrict to bounded side windows by
      `SCV.exists_localEOW_truncatedSideCones_for_sliceMargin`.  The checked
      `SCV/LocalEOWChartEnvelope.lean` bridge now records the strict
      chart-side version: positive/negative strict coordinate balls are open,
      and `localEOWChart x0 ys` sends them into the `TubeDomain`s over
      `localEOWSideCone ys ε ∩ ball 0 rside` and its negative image by the
      identity
      `Im (localEOWChart x0 ys w) = localEOWRealLinearPart ys (Im w)`.
      It also records the fixed-window coordinate-sum facts that the Rudin
      side theorem actually consumes: a strict positive ball point has
      nonnegative imaginary coordinates, positive coordinate sum, and sum
      bounded by `card * R`; the strict negative ball has the corresponding
      statement for `-Im w`.  Therefore the final local scale is chosen by
      `SCV.exists_oneChartRecoveryScale`, not by ad hoc inequalities: with
      `Rcore = σ`, `rker = σ`, and `Rdesc = 4 * σ`, it gives
      `(Fintype.card (Fin m) : ℝ) * Rdesc < rpoly`, `Rdesc < δside`, and
      `Rdesc < ρin`.  The fixed-window side membership on the final core and
      on the larger approximate-identity side neighborhood is discharged by
      `SCV.localEOWChart_mem_fixedWindow_of_strictPositiveImagBall` and
      `SCV.localEOWChart_mem_fixedWindow_of_strictNegativeImagBall`.
      Thus the one-chart theorem does not need to reprove, or silently assume,
      that chart imaginary coordinates are original edge coordinates.  The
      affine real-window factor is likewise checked as
      `SCV.localEOWAffineRealWindow`: it is open, contains
      `localEOWChart x0 ys w` when the coordinate real part of `w` is small,
      and expands from `2ρ` to `3ρ` under `z + realEmbed t` exactly when
      `‖(localEOWRealLinearCLE ys hli).symm t‖ < ρ`.  The checked
      `SCV.chartSlowGrowth_from_uniformConeSlowGrowth` theorem remains an
      outer OS-II adapter if one is constructing `hplus_bv`/`hminus_bv` from
      slow-growth data, but it is not consumed by this one-chart core.
   9. Choose nested chart boxes `B0 ⋐ B1 ⋐ Echart` and a support radius
      `rψ > 0` so `u ∈ B0` and `t ∈ closedBall 0 rψ` imply `u + t ∈ B1`.
      The checked closed-ball version is
      `SCV.localEOW_closedBall_support_margin`: from `ρ > 0`, take
      `B0 = Metric.closedBall 0 (ρ/2)`, `B1 = Metric.closedBall 0 ρ`, and
      `rψ = ρ/2`.  Shrink the positive and negative polywedges over `B0` so
      every real translate by such `t` remains inside the corresponding large
      local wedge over `B1`.
   10. For each compactly supported Schwartz kernel `ψ` with
      `tsupport ψ ⊆ closedBall 0 rψ`, form the real-direction regularizations
      `Fplusψ z = ∫ t, FplusChart (z + realEmbed t) * ψ t` and
      `Fminusψ z = ∫ t, FminusChart (z + realEmbed t) * ψ t`.  Prove these are
      holomorphic on the shrunken chart polywedges by the local version of
      `SCV.differentiableOn_realMollify_tubeDomain`.
   11. Define the common continuous boundary value in original real-edge
       coordinates first:
       `bvψ u = TcutOrig (translateSchwartz (-u) ψ)`.
       The proof is the checked CLM route, not an informal Fubini step:
       construct the side slice CLMs with
       `SCV.localEOWSliceCLMs_from_preparedDomains`, use
       `realMollifyLocal_eq_cutoffSliceCLM` for the finite-support integral
       identity, use the cutoff-support slice limits targeting `TcutOrig` for
       the plus/minus limits, and then apply
       `SCV.localRealMollify_commonContinuousBoundary_of_clm` to obtain
       continuity of `bvψ` and the two continuous boundary traces.  The
       coordinate-cone plumbing is fixed as follows: the plus raw limit is on
       `Cplus = localEOWSideCone ys ε`, and the minus raw limit is on
       `Cminus = Neg.neg '' Cplus`.  The bounded sets
       `CplusLoc = Cplus ∩ ball 0 rside` and
       `CminusLoc = Neg.neg '' CplusLoc` provide the honest side margins for
       the cutoff slice theorem.  For final strict positive chart-side balls,
       `localEOWRealLinearPart ys v` lies in `CplusLoc` by the checked
       positive-coordinate side-cone lemma plus the small linear-image radius;
       for strict negative balls, apply the same argument to `-v` and then use
       the negative-image identity.  This sign check is part of the proof, not
       a convention left to tactic search.  Only after the real kernel is
       pushed by `localEOWRealLinearKernelPushforwardCLM` is the chart
       distribution
       `localEOWAffineDistributionPullbackCLM x0 ys hli TcutOrig` recovered.
   12. Apply `SCV.local_continuous_edge_of_the_wedge_envelope` to the
       regularized pair for each `ψ`, producing `Gψ` on one fixed neighborhood
       `U0` determined only by `B0`, `B1`, `C`, and `rψ`.  The extracted local
       continuous EOW theorem must include uniqueness on `U0`; this is what
       makes linearity in `ψ` and real-translation covariance provable without
       arbitrary-choice artifacts.
   13. Prove the local Streater-Wightman recovery package.  The old global
       theorem surface
       `SCV.regularizedLocalEOW_productKernel_from_continuousEOW` is retired:
       a complex-chart cutoff extension of the local pairing does not produce
       `ProductKernelRealTranslationCovariantGlobal K`.  The route is now the
       local descent package from `docs/scv_infrastructure_blueprint.md`,
       using chart-coordinate smoothing kernels throughout.

      The checked fixed-window theorem remains the starting point:

      ```lean
      theorem SCV.regularizedLocalEOW_family_from_fixedWindow
          {m : ℕ} {r : ℝ}
          (hm : 0 < m) (hr : 0 < r)
          -- same fixed chart/window, margin, CLM, and slice-limit
          -- hypotheses as `regularizedLocalEOW_fixedWindowEnvelope_from_clm`,
          -- uniformly for all `ψ` with `KernelSupportWithin ψ r`
          :
          let G : SchwartzMap (Fin m -> ℝ) ℂ ->
              ComplexChartSpace m -> ℂ :=
            fun ψ w =>
              localRudinEnvelope δ x0 ys
                (realMollifyLocal Fplus ψ)
                (realMollifyLocal Fminus ψ) w
          ...
      ```

      For recovery, however, the family used in the product variable is the
      chart-kernel family

      ```lean
      def Gchart (ψ : SchwartzMap (Fin m -> ℝ) ℂ)
          (w : ComplexChartSpace m) : ℂ :=
        G (SCV.localEOWRealLinearKernelPushforwardCLM ys hli ψ) w
      ```

      The pushforward is mandatory: `localEOWChart x0 ys (w - realEmbed a)`
      translates the original real edge by
      `SCV.localEOWRealLinearPart ys a`, not by `a`.

      The local descent theorem surfaces, in exact order, are:

      1. `SCV.regularizedLocalEOW_pairingCLM_of_fixedWindow`.  It constructs a
         genuine mixed Schwartz CLM `K` by fixed cutoffs: a complex-chart
         cutoff `χU`, a chart-kernel cutoff `χr`, and the original-edge cutoff
         hidden inside the value CLM for the pushed kernel.  Here
         `P = localEOWRealLinearKernelPushforwardCLM ys hli` and
         ```
         Gorig η z =
           localRudinEnvelope δ x0 ys
             (realMollifyLocal Fplus η)
             (realMollifyLocal Fminus η) z.
         ```
         The theorem is stated after the value-CLM and continuity helpers have
         supplied the exact inputs `Lchart`, `hLchart_cutoff`,
         `hLchart_value`, `hLchart_bound`, `hcont_integrand`, and `hG_holo`;
         this avoids repeating the full fixed-window hypothesis block while
         still constructing a real mixed Schwartz CLM.  Its definition is:
         ```lean
         K F =
           ∫ z in closedBall 0 Rcut, χU z *
             Gorig (χψ • P (χr • schwartzPartialEval₁CLM z F)) z
         ```
         where `Lchart z` is
         `Lorig z ∘ localEOWRealLinearKernelPushforwardCLM ys hli ∘ (χr • ·)`.
         The integral is defined from the actual cutoff envelope expression,
         not from the choice-valued map `z ↦ Lchart z`; `Lchart` is used for
         linearity and bounds after the integrand has been shown continuous.
         The proof must include the complex-chart cutoff theorem, the
         SCV-local `schwartzPartialEval₁CLM` and compact seminorm estimate,
         the compact-uniform value-CLM bound for `Lorig`, support-radius
         monotonicity for pushed kernels, finite-seminorm transport through the
         composed kernel Schwartz CLM, continuity of the varying-slice cutoff
         envelope integrand, and the cutoff-removal proof on tests supported
         in `Ucov`.  The pure-tensor representation must use the local
         support-integral package now pinned in
         `docs/scv_infrastructure_blueprint.md`:
         `continuous_mul_of_continuousOn_supportsInOpen`,
         `integrable_mul_of_continuousOn_supportsInOpen`, and
         `closedBall_setIntegral_mul_eq_integral_of_supportsInOpen`.  These
         are the exact facts that justify the all-space integral
         `∫ z, Gchart ψ z * φ z` from continuity of `Gchart ψ` only on
         `Ucov` and `tsupport φ ⊆ Ucov`; the proof must not assume global
         measurability or continuity of `Gchart ψ`.
      2. `SCV.regularizedLocalEOW_pairingCLM_localCovariant` is now checked in
         `SCV/LocalEOWPairingCLM.lean`.  It proves
         `ProductKernelRealTranslationCovariantLocal K Ucov r`, not global
         covariance.  The proof expands both product pairings, changes
         variables in the complex-chart integral by the support-localized lemma
         `integral_mul_complexTranslateSchwartz_eq_shift_of_support`, and uses
         `SCV.regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap`
         on the support of `φ`.  The theorem surface includes the local
         continuity input `hG_cont` on the covariance ball, derived from the
         fixed-window holomorphy of the regularized family, solely to justify
         this all-space integral change of variables.  That helper must take
         compact support of `φ` and the explicit fact
         `tsupport φ` translates backward into `Ucov`; otherwise the
         right-hand shifted integrand would again be relying on hidden global
         regularity of `Gchart ψ`.  The backward translation fact is not a
         pointwise-support shortcut: it is supplied by the named
         topological-support transport lemma
         `tsupport_subset_preimage_tsupport_complexTranslateSchwartz`, proved
         from `tsupport_comp_subset_preimage` applied to the inverse
         translation and the identity
         `complexTranslateSchwartz a φ (z - realEmbed a) = φ z`.  If `φ` is
         nonzero, the
         support hypotheses for
         both `φ` and `complexTranslateSchwartz a φ` give witnesses
         `u ∈ Ucov` and `u - realEmbed a ∈ Ucov`, hence
         `‖a‖ < 2 * Rcov < δ / 4`; if `φ = 0`, the covariance identity is
         trivial.  The conversion from the complex-chart displacement to
         `‖a‖` uses the required finite sup-norm equality
         `norm_realEmbed_eq`, whose reverse direction is proved coordinatewise
         from `norm_le_pi_norm (realEmbed a) i` and `Complex.norm_real`.  The
         sign is the checked convention
         `complexTranslateSchwartz a φ z = φ (z + realEmbed a)`, so the
         changed left integrand is `Gchart ψ (z - realEmbed a) * φ z`, and
         `hG_cov` rewrites it to
         `Gchart (translateSchwartz a ψ) z * φ z` only after splitting on
         `φ z = 0`: the zero branch is immediate, while the nonzero branch
         gives `z ∈ Function.support φ ⊆ tsupport φ` and then both
         `z ∈ Ucov` and `z - realEmbed a ∈ Ucov`.  No global regularity of
         `Gchart ψ` is used.
      3. `SCV.translationCovariantProductKernel_descends_local`.  It defines
         `Hdist := complexRealFiberTranslationDescentCLM
           (shearedProductKernelFunctional K) η` with a normalized real
         cutoff `η`, but it does not call the checked global arbitrary-test
         fiber quotient.  Instead it proves a scalarized local quotient theorem
         for the single sheared product pair; no `SchwartzMap`-valued Bochner
         integral is introduced.  The local quotient first proves
         fixed-fiber partial evaluation and
         `mixedRealFiberIntegralCLM` with
         `continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral`,
         so every parameter integral after applying `K` is an ordinary complex
         integral.  The mixed integral CLM is constructed directly by
         `SchwartzMap.mkCLM` and finite seminorm estimates; the already checked
         `HeadBlockIntegral.integrateHeadBlock` remains a source pattern, not
         the CLM used here.  The scalarization theorem is not a hidden
         `SchwartzMap`-valued Bochner step: it constructs
         `mixedRealFiberIntegralScalarCLM K` by finite Schwartz-seminorm
         bounds.  The key bound is the named decay theorem
         `schwartzPartialEval₂CLM_finsetSeminorm_decay`: for every finite
         output-seminorm family, partial evaluation at parameter `a` is
         bounded by an integrable factor
         `(1 + ‖a‖)^(-volume.integrablePower)` times finitely many source
         seminorms of the triple Schwartz test.  Its proof uses the two
         source weights `(k,l)` and `(k+volume.integrablePower,l)` to control
         the origin and the tail separately.  The scalar CLM is then
         identified with `K.comp mixedRealFiberIntegralCLM` on the dense span
         of split `mixedBaseFiberTensor` tests, using the exact tensor
         identities
         `schwartzPartialEval₂CLM_mixedBaseFiberTensor` and
         `mixedRealFiberIntegralCLM_mixedBaseFiberTensor`, and then extends by
         continuity using `mixedBaseFiberProductTensorDense_all`.  It then
         uses local covariance only for parameters whose nonzero kernel factor
         `κ a = η • translateSchwartz a ψ` forces
         `‖a‖ ≤ r + rη`.  The normalized cutoff enters through
         `complexRealFiberIntegral_schwartzTensorProduct₂` and `∫ η = 1`.
         The margin
         `Udesc + closedBall 0 (r + rη) ⊆ Ucov` is exactly what makes the two
         complex-chart supports legal in those covariance calls, and the two
         kernel-support inputs are obtained by support containment in
         `tsupport η` and `tsupport ψ`, followed by monotonicity to radius
         `r + rη`.  The compact-support half of
         `SupportsInOpen (complexTranslateSchwartz (-a) φ) Ucov` is a named
         translation-support helper, not an implicit property of the support
         inclusion.  The local-descent CLEs use an explicit local
         `realEmbedContinuousLinearMap`; the older `realEmbedCLM` helpers are
         private implementation details and are not part of the route API.
      4. `SCV.regularizedEnvelope_chartEnvelope_from_localProductKernel`.  It
         consumes local distributional holomorphy of `Hdist` on `Udesc`; the
         CR proof is a separate immediately preceding step, not a hidden field.
         That step uses the local descent identity and the checked `∂bar`
         product integral theorem in its localized form: `hK_rep` is used only
         after enlarging `SupportsInOpen (dbarSchwartzCLM j φ)` from `Udesc`
         to `Ucov`, while holomorphy is restricted from `U0` back to `Udesc`.
         With `hCR` supplied this way, the recovery theorem applies
         `SCV.distributionalHolomorphic_regular`, the checked pointwise
         representation bridge with `Ucore ⊂ Udesc`, and the checked
         delta-limit wedge-agreement theorem.

      The fixed-window family theorem already checked in Lean supplies:

         ```lean
         theorem SCV.regularizedLocalEOW_family_from_fixedWindow
             {m : ℕ} {r : ℝ}
             (hm : 0 < m) (hr : 0 < r)
             -- same fixed chart/window, margin, CLM, and slice-limit
             -- hypotheses as `regularizedLocalEOW_fixedWindowEnvelope_from_clm`,
             -- uniformly for all `ψ` with `KernelSupportWithin ψ r`
             :
             let G : SchwartzMap (Fin m -> ℝ) ℂ ->
                 ComplexChartSpace m -> ℂ :=
               fun ψ w =>
                 localRudinEnvelope δ x0 ys
                   (realMollifyLocal Fplus ψ)
                   (realMollifyLocal Fminus ψ) w
             (∀ ψ, KernelSupportWithin ψ r ->
               DifferentiableOn ℂ (G ψ) U0) ∧
               (∀ ψ, KernelSupportWithin ψ r ->
                 ∀ z ∈ Ucore ∩ DplusSmall,
                   G ψ z = realMollifyLocal Fplus ψ z) ∧
               (∀ ψ, KernelSupportWithin ψ r ->
                 ∀ z ∈ Ucore ∩ DminusSmall,
                   G ψ z = realMollifyLocal Fminus ψ z) ∧
               (∀ ψ, KernelSupportWithin ψ r ->
                 ∀ u : Fin m -> ℝ,
                   (fun j => (u j : ℂ)) ∈ U0 ->
                     G ψ (fun j => (u j : ℂ)) =
                       Treal
                         (translateSchwartz
                           (-(localEOWRealChart x0 ys u)) ψ)) ∧
               (∀ ψ, KernelSupportWithin ψ r ->
                 ∀ H : ComplexChartSpace m -> ℂ,
                   DifferentiableOn ℂ H U0 ->
                   (∀ w ∈ U0, (∀ j, 0 < (w j).im) ->
                     H w = realMollifyLocal Fplus ψ
                       (localEOWChart x0 ys w)) ->
                   ∀ w ∈ U0, H w = G ψ w)
         ```

         Additivity and complex homogeneity on the supported-kernel class are
         checked as `SCV.regularizedLocalEOW_family_add` and
         `SCV.regularizedLocalEOW_family_smul`.  The chart-linear transport,
         support transport, and translated side-branch identity are also
         checked in `SCV/LocalEOWChartLinear.lean` and
         `SCV/LocalDistributionalEOW.lean`; the current covariance substrate is
         `SCV.regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap`.

      The Lean implementation has checked the first helper layers feeding the
      pairing CLM: complex-chart cutoff, `SupportsInOpen` cutoff removal, and
      the SCV-local `schwartzPartialEval₁CLM` apply/tensor/seminorm package,
      plus the compact value-CLM bound for `Lorig`.  The next chart-kernel
      helpers are also checked: the generic
      `SCV/SchwartzPartialEval.lean` first-variable continuity port, the
      public kernel API theorem `continuous_schwartzPartialEval₁CLM`,
      `KernelSupportWithin.mono`,
      `SchwartzMap.exists_schwartzCLM_finsetSeminormBound`, and
      `regularizedLocalEOW_chartKernelFamily_valueCLM`.  The checked
      chart-kernel theorem consumes the original-family compact value-CLM
      package and proves the chart cutoff removal, pushforward support
      enlargement `‖A‖ * rcut ≤ rψ`, original-edge cutoff removal, and
      composed finite-seminorm bound explicitly.  The chart-linear API is part
      of this gate: `localEOWRealLinearPushforwardCLM_apply`,
      `KernelSupportWithin.localEOWRealLinearPushforwardCLM`,
      `localEOWRealLinearKernelPushforwardCLM_apply`, and
      `KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM` are checked,
      and the kernel pushforward includes the inverse absolute determinant
      factor.  The mollifier change-of-variables theorem
      `realMollifyLocal_localEOWRealLinearKernelPushforwardCLM` rewrites the
      original-edge mollifier into the chart-coordinate integral, while
      `realMollifyLocal_localEOWChart_translate_kernelPushforwardCLM` is the
      translated side-branch identity used by fixed-window covariance.

      The mixed pairing CLM gate is now closed.  The formerly pending theorem
      `continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand` is checked,
      so the set integral defining `K` is an integral of the actual continuous
      cutoff envelope and not of an arbitrary choice of `Lchart z`.  The
      checked layer in `SCV/VaryingKernelContinuity.lean` contains:
      continuity of the cutoff slice, varying-kernel real-mollifier continuity
      with fixed compact support and an open original side domain, the
      real-seminorm uniform-on-compact translation estimate controlling both
      `k,l` and `0,l` seminorms, fixed-support joint continuity of
      `(z,u) ↦ translateSchwartz (-u) (η z)`, the varying-kernel
      Rudin-envelope dominated-continuity theorem, the parametric
      Rudin-integrand compact-bound theorem, the scalar
      evaluation/support theorems for the actual chart-kernel slice, and
      the boundary-CLM continuity component of the CLM boundary-data theorem.
      The plus and minus moving-kernel side-limit theorems
      `tendsto_localRudinPlusBoundary_varyingKernel_of_clm` and
      `tendsto_localRudinMinusBoundary_varyingKernel_of_clm` are now checked
      in `SCV/VaryingKernelContinuity.lean`, with vector-valued
      `hkernel_cont` as the Banach-Steinhaus input.  The bundled
      `localRudin_varyingKernel_boundaryData_of_clm` is also checked: it
      derives `hkernel_cont`, returns scalar `hbv_cont`, and packages the two
      side limits.  The final cutoff-envelope continuity theorem
      `SCV.continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand` is now
      checked too.  The support-integral helper surfaces named above are now
      checked in `SCV/DistributionalEOWSupport.lean`, and the mixed pairing
      CLM is checked in `SCV/LocalEOWPairingCLM.lean` as
      `SCV.regularizedLocalEOW_pairingCLM_of_fixedWindow`.  It is constructed
      by the actual closed-ball cutoff-envelope integral and the explicit
      `SchwartzMap.mkCLMtoNormedSpace` estimate: use the finite-seminorm data
      from `hLchart_bound`, compose it with
      `schwartzPartialEval₁CLM_compactSeminormBound`, bound `χU` only on
      `closedBall 0 Rcut`, and multiply by
      `(volume (Metric.closedBall 0 Rcut)).toReal`; no support hypothesis on
      `χU` is part of this theorem.
      The checked parametric bound theorem only uses continuity of
      `Fplus`/`Fminus` on the original side domains;
      differentiability of the mollified side functions on `Dplus`/`Dminus`
      is derived separately for the measurability input to dominated
      continuity.  The boundary limits in that stack
      cannot be fixed-`z` limits: the kernel varies along the approaching
      Rudin arc.  The proof combines the checked local BHW/EOW side-value
      identities, the existing CLM boundary limits, and
      `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`; the
      moving-kernel convergence is exactly the fixed-support joint translation
      helper as a Schwartz-valued continuity statement, not merely the scalar
      `Tchart`-applied continuity.  The bundled boundary-data theorem derives
      both: vector-valued `hkernel_cont` for Banach-Steinhaus, then scalar
      `hbv_cont` by composing with `Tchart.continuous`.  The last congruence
      in each side-limit is also fixed: after
      `hplus_eval` or `hminus_eval`, the side identity has
      `translateSchwartz (fun i => -(sample p i).re)`, and the target moving
      kernel has `translateSchwartz (-(realSample p))`; these are definitionally
      reconciled by the local real-coordinate equality
      `fun i => -(sample p i).re = -(realSample p)` obtained from
      `localEOWChart`/`localEOWRealChart` (equivalently
      `localEOWChart_real_imag`).  Only after those targets are checked should
      Lean introduce
      `regularizedLocalEOW_pairingCLM_of_fixedWindow`; it must not revive the
      retired global `regularizedLocalEOW_productKernel_from_continuousEOW`
      surface.  Its pure-tensor all-space integral representation must first
      prove the closed-ball identity by rewriting the actual integrand through
      `hLchart_cutoff`, using `schwartzPartialEval₁CLM_tensorProduct₂`,
      pulling `φ z` through `Lchart z`, applying `hLchart_value` to the
      supported kernel `ψ`, and removing `χU` on `tsupport φ`.  Only then may
      it invoke
      `closedBall_setIntegral_mul_eq_integral_of_supportsInOpen`, deriving
      `ContinuousOn (Gchart ψ) Ucov` from `hG_holo` and
      `Ucov ⊆ closedBall 0 Rcut ⊆ ball 0 (δ / 2)`.  Thus the all-space
      integrand is the closed-ball continuous integrand extended by zero, so
      no global measurability of `Gchart ψ` is assumed.  In the final
      `SCV.local_distributional_edge_of_the_wedge_envelope`
      implementation, `hcontinuousEOW` is not an extra assumption: it is
      obtained inside the proof by applying
      `SCV.localRealMollify_commonContinuousBoundary_of_clm` to `hplus_eval`,
      `hminus_eval`, `hplus_limit`, and `hminus_limit`, followed by the
      extracted local continuous EOW theorem.

   14. Let `ψρ` be the checked compactly supported approximate identity in
       chart-kernel coordinates, with support eventually inside
       `closedBall 0 r`.  On the positive and negative wedge pieces, the side
       identities for `Gchart ψρ` reduce to real mollification with the pushed
       kernels, and the checked approximate-identity theorem gives convergence
       to `FplusChart` and `FminusChart`.  The translate-margin hypotheses for
       those approximate-identity calls are not implicit: for
       `z ∈ StrictPositiveImagBall σ` or `z ∈ StrictNegativeImagBall σ` and
       `‖t‖ ≤ σ`, the checked strict-side real-translation lemmas place
       `z + realEmbed t` in `Metric.ball 0 (4 * σ)` with the same strict side
       sign.  The checked
       `regularizedEnvelope_chartEnvelope_from_localCovariantProductKernel`
       constructs `Hdist`, proves local distributional holomorphy from local
       covariance, and proves that the same sequence converges pointwise to
       the holomorphic representative `H` on `Ucore`.  Thus `H` is the desired
       local distributional EOW envelope on the fixed chart window.
   15. Transport this coordinate envelope through
       `A = SCV.localEOWComplexAffineEquiv x0 ys hli`:
       `Uorig = A '' Ucore`, `UplusOrig = A '' DplusSmall`,
       `UminusOrig = A '' DminusSmall`, and
       `Horig z = H (A.symm z)`.  The transport lemmas prove openness of
       these images, holomorphy of `Horig`, real-slice membership
       `realEmbed x0 ∈ Uorig`, and side agreements with the original
       `Fplus`/`Fminus`.
   16. Patch the transported chart envelopes over the real edge cover.  Because
       every patch uses the same global basis `ys`, overlap compatibility is
       by the ordinary identity theorem on a common positive side window:
       conjugation invariance and convexity put a real point `p` in any
       nonempty overlap.  If `p` has real coordinates `u₁,u₂` in the two
       charts, choose one small vector `v` with `∀ j, 0 < v j`; then
       `localEOWChart x₁ ys (u₁ + I v)` and
       `localEOWChart x₂ ys (u₂ + I v)` are the same original point
       `p + I * localEOWRealLinearPart ys v`.  For `v` small enough this point
       lies in both transported positive side windows, and both transported
       envelopes equal `Fplus` there.  This is the fixed-basis version of the
       now-public
       `SCV.local_extensions_consistent` pattern.
   17. Extract the connected component needed by the OS45 consumer only after
       the local extension `U,F` exists; connectedness is not an input to the
       SCV theorem.

   This proof is pure complex analysis/distribution theory.  It is the place
   where the standard Streater-Wightman/Jost distributional EOW theorem is
   proved in the repo's SCV layer; it is not another locality theorem.

7. The OS45 instantiation of this SCV theorem must use a local wedge, not an
   arbitrary placeholder domain.  The Lean-facing theorem remains
   `BHW.os45_adjacent_commonBoundaryEnvelope`, but its internal data are fixed
   as follows:

   ```lean
   let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
   let Qρe := BHW.os45CommonChartCLE (d := d) (n := n) ρ
   let Ecommon : Set (NPointDomain d n) :=
     BHW.os45CommonEdgeRealPoint (d := d) (n := n) ρ '' V

   let Ωplus : Set (Fin n -> Fin (d + 1) -> ℂ) :=
     {z |
       BHW.permAct (d := d) ρ (Qρe.symm z) ∈
         AnalyticContinuationRegion d n 1 ∧
       BHW.permAct (d := d) (τ.symm * ρ)
         (BHW.permAct (d := d) τ (Qρe.symm z)) ∈
         AnalyticContinuationRegion d n 1}

   let Ωminus : Set (Fin n -> Fin (d + 1) -> ℂ) :=
     BHW.os45PulledRealBranchDomain (d := d) (n := n) ρ ∩
       BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ)

   let Hplus : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ := fun z =>
     bvt_F OS lgc n (BHW.permAct (d := d) τ (Qρe.symm z)) -
       bvt_F OS lgc n (Qρe.symm z)

   let Hminus : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ := fun z =>
     BHW.os45PulledRealBranch (d := d) (n := n) OS lgc (τ.symm * ρ) z -
       BHW.os45PulledRealBranch (d := d) (n := n) OS lgc ρ z
   ```

   Required OS45 proof slots, in order:

   1. `Ωplus` and `Ωminus` are open.  The negative side uses
      `isOpen_os45PulledRealBranchDomain`; the positive side uses openness of
      `AnalyticContinuationRegion d n 1`, supplied by
      `isOpen_analyticContinuationRegion_succ`, under the explicit
      continuous-linear maps.
   2. `Hplus` is holomorphic on `Ωplus`; use
      `(bvt_F_acrOne_package (d := d) OS lgc n).1`, the total permutation
      symmetry field `(bvt_F_acrOne_package (d := d) OS lgc n).2.2.1`, and
      differentiability of `Qρe.symm` and finite coordinate permutations.
   3. `Hminus` is holomorphic on `Ωminus`; use
      `BHW.os45PulledRealBranch_holomorphicOn` on each factor and restrict to
      the intersection.
   4. The trace membership facts are already checked in
      `OSToWightmanLocalityOS45TraceMembership.lean`:

      ```lean
      theorem BHW.adjacent_wick_traces_mem_acrOne
          (i : Fin n) (hi : i.val + 1 < n)
          (ρ : Equiv.Perm (Fin n))
          {x : NPointDomain d n}
          (hx_ordered :
            x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
          (hx_swap_ordered :
            (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
              EuclideanOrderedPositiveTimeSector (d := d) (n := n)
                ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
          BHW.permAct (d := d) ρ (fun k => wickRotatePoint (x k)) ∈
              AnalyticContinuationRegion d n 1 ∧
          BHW.permAct (d := d) ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
              (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                (fun k => wickRotatePoint (x k))) ∈
              AnalyticContinuationRegion d n 1

      theorem BHW.os45CommonChart_real_mem_pulledRealBranchDomain_pair
          (τ ρ : Equiv.Perm (Fin n))
          {x : NPointDomain d n}
          (hx_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n)
          (hxτ_ET : BHW.realEmbed (fun k => x (τ k)) ∈
            BHW.ExtendedTube d n) :
          BHW.os45CommonChartCLE (d := d) (n := n) ρ (BHW.realEmbed x) ∈
            BHW.os45PulledRealBranchDomain (d := d) (n := n) ρ ∩
              BHW.os45PulledRealBranchDomain (d := d) (n := n)
                (τ.symm * ρ)
      ```

      They provide the two ACR-one memberships for the Wick trace and both
      pulled real-branch-domain memberships for the real trace.
   5. Build the local wedge hypothesis for
      `SCV.local_distributional_edge_of_the_wedge_envelope` from
      `OS45OppositeTubeBranchGeometry`.  The theorem to prove in Lean is:

      ```lean
      theorem BHW.os45_commonChart_localWedge
          [NeZero d]
          (i : Fin n) (hi : i.val + 1 < n)
          (V : Set (NPointDomain d n))
          (ρ : Equiv.Perm (Fin n))
          (hV_open : IsOpen V)
          (hV_geom :
            ∀ x ∈ V, OS45OppositeTubeBranchGeometry (d := d) (n := n) ρ x)
          (hV_swap_geom :
            ∀ x ∈ V,
              OS45OppositeTubeBranchGeometry (d := d) (n := n)
                ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
                (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
          (Ωplus Ωminus : Set (Fin n -> Fin (d + 1) -> ℂ))
          (Ecommon Ccommon : Set (NPointDomain d n))
          (hΩplus_open : IsOpen Ωplus)
          (hΩminus_open : IsOpen Ωminus)
          (hEcommon :
            Ecommon = os45CommonEdgeRealPoint (d := d) (n := n) ρ '' V)
          (hCcommon : Ccommon = {η | InForwardCone d n η}) :
          ∀ K : Set (NPointDomain d n), IsCompact K -> K ⊆ Ecommon ->
            ∀ Kη : Set (NPointDomain d n), IsCompact Kη -> Kη ⊆ Ccommon ->
              ∃ r : ℝ, 0 < r ∧
                ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
                  (fun a μ => (x a μ : ℂ) +
                    (ε : ℂ) * (η a μ : ℂ) * Complex.I) ∈ Ωplus ∧
                  (fun a μ => (x a μ : ℂ) -
                    (ε : ℂ) * (η a μ : ℂ) * Complex.I) ∈ Ωminus
      ```

      Proof: pull `K` back through `os45CommonEdgeRealCLE ρ`; for each source
      point use the two geometry packets to get the exact plus/minus trace
      directions; use openness of `Ωplus/Ωminus` and compactness of `K × Kη`
      to choose one radius.  The compact direction set must be a compact
      subcone of `InForwardCone d n`, not a single radial direction.
   6. Prove local slow growth for both sides.  These are genuine estimates, not
      optional assumptions:

      ```lean
      theorem BHW.os45_Hplus_slowGrowth_compactSubcone
          [NeZero d]
          (OS : OsterwalderSchraderAxioms d)
          (lgc : OSLinearGrowthCondition d OS)
          (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
          (ρ : Equiv.Perm (Fin n))
          (Ecommon Ccommon : Set (NPointDomain d n))
          (Hplus : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) :
          ∀ K : Set (NPointDomain d n), IsCompact K -> K ⊆ Ecommon ->
            ∀ Kη : Set (NPointDomain d n), IsCompact Kη -> Kη ⊆ Ccommon ->
              ∃ (A : ℝ) (N : ℕ) (r : ℝ), 0 < A ∧ 0 < r ∧
                ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
                  ‖Hplus (fun a μ => (x a μ : ℂ) +
                    (ε : ℂ) * (η a μ : ℂ) * Complex.I)‖ ≤ A * (ε⁻¹) ^ N

      theorem BHW.os45_Hminus_slowGrowth_compactSubcone
          [NeZero d]
          (OS : OsterwalderSchraderAxioms d)
          (lgc : OSLinearGrowthCondition d OS)
          (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
          (ρ : Equiv.Perm (Fin n))
          (Ecommon Ccommon : Set (NPointDomain d n))
          (Hminus : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) :
          ∀ K : Set (NPointDomain d n), IsCompact K -> K ⊆ Ecommon ->
            ∀ Kη : Set (NPointDomain d n), IsCompact Kη -> Kη ⊆ Ccommon ->
              ∃ (A : ℝ) (N : ℕ) (r : ℝ), 0 < A ∧ 0 < r ∧
                ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε -> ε < r ->
                  ‖Hminus (fun a μ => (x a μ : ℂ) -
                    (ε : ℂ) * (η a μ : ℂ) * Complex.I)‖ ≤ A * (ε⁻¹) ^ N
      ```

      The plus estimate comes from the growth field of
      `full_analytic_continuation_with_acr_symmetry_growth OS lgc n`, transported
      through the two finite permutation/OS45 common-chart linear maps and
      combined by `norm_sub_le`.  The minus estimate comes from the same
      forward-tube growth after the BHW `extendF` branch representation:
      cover the compact OS45 real-branch patch by finitely many Lorentz charts
      in `ExtendedTube`; on each chart use `forward_tube_lorentz_growth`, then
      take the maximum of the finitely many constants.
   7. Prove the two compact-subcone-uniform distributional boundary-value
      hypotheses by transporting OS-II ACR-one boundary values to the common
      chart.  The Lean surfaces are:

      ```lean
      theorem BHW.os45_Hplus_commonBoundary_uniform
          [NeZero d]
          (OS : OsterwalderSchraderAxioms d)
          (lgc : OSLinearGrowthCondition d OS)
          (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
          (V Ecommon Ccommon : Set (NPointDomain d n))
          (ρ : Equiv.Perm (Fin n))
          (Tcommon : SchwartzMap (NPointDomain d n) ℂ ->L[ℂ] ℂ)
          (Hplus : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) :
          ∀ Kη : Set (NPointDomain d n), IsCompact Kη -> Kη ⊆ Ccommon ->
            ∀ φ : SchwartzMap (NPointDomain d n) ℂ,
              HasCompactSupport (φ : NPointDomain d n -> ℂ) ->
              tsupport (φ : NPointDomain d n -> ℂ) ⊆ Ecommon ->
              TendstoUniformlyOn
                (fun ε η =>
                  ∫ x : NPointDomain d n,
                    Hplus (fun a μ => (x a μ : ℂ) +
                      (ε : ℂ) * (η a μ : ℂ) * Complex.I) * φ x)
                (fun _ : NPointDomain d n => Tcommon φ)
                (nhdsWithin 0 (Set.Ioi 0))
                Kη

      theorem BHW.os45_Hminus_commonBoundary_uniform
          [NeZero d]
          (OS : OsterwalderSchraderAxioms d)
          (lgc : OSLinearGrowthCondition d OS)
          (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
          (V Ecommon Ccommon : Set (NPointDomain d n))
          (ρ : Equiv.Perm (Fin n))
          (Tcommon : SchwartzMap (NPointDomain d n) ℂ ->L[ℂ] ℂ)
          (Hminus : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) :
          ∀ Kη : Set (NPointDomain d n), IsCompact Kη -> Kη ⊆ Ccommon ->
            ∀ φ : SchwartzMap (NPointDomain d n) ℂ,
              HasCompactSupport (φ : NPointDomain d n -> ℂ) ->
              tsupport (φ : NPointDomain d n -> ℂ) ⊆ Ecommon ->
              TendstoUniformlyOn
                (fun ε η =>
                  ∫ x : NPointDomain d n,
                    Hminus (fun a μ => (x a μ : ℂ) -
                      (ε : ℂ) * (η a μ : ℂ) * Complex.I) * φ x)
                (fun _ : NPointDomain d n => Tcommon φ)
                (nhdsWithin 0 (Set.Ioi 0))
                Kη
      ```

      The common boundary functional `Tcommon` is the compact-test distribution
      on the common edge obtained from
      `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector` after the
      `os45CommonEdgeRealCLE ρ` change of variables.  The plus side uses
      `bvt_boundary_values` / `bvt_F_acrOne_package`; the minus side uses the
      BHW branch pullback theorem defining `os45PulledRealBranch` and the same
      common-edge test after the OS45 chart.  No locality theorem, PET
      branch-independence theorem, or boundary-locality transfer theorem may
      appear in this proof.

      The phrase "uses `bvt_boundary_values`" hides one genuine OS-II
      strengthening that must be implemented before the SCV theorem can be
      consumed.  The checked theorem `bvt_boundary_values` is raywise in the
      forward-cone direction `η`; the SCV envelope theorem needs
      `TendstoUniformlyOn` over every compact direction set `Kη`.  The required
      Lean-facing strengthening is:

      ```lean
      theorem bvt_boundary_values_uniformOnCompactDirections
          [NeZero d]
          (OS : OsterwalderSchraderAxioms d)
          (lgc : OSLinearGrowthCondition d OS)
          (n : ℕ)
          (Kη : Set (NPointDomain d n))
          (hKη_compact : IsCompact Kη)
          (hKη_sub : Kη ⊆ ForwardConeAbs d n)
          (φ : SchwartzMap (NPointDomain d n) ℂ)
          (hφ_compact : HasCompactSupport (φ : NPointDomain d n -> ℂ)) :
          TendstoUniformlyOn
            (fun ε η =>
              ∫ x : NPointDomain d n,
                bvt_F OS lgc n
                  (fun k μ => (x k μ : ℂ) +
                    (ε : ℂ) * (η k μ : ℂ) * Complex.I) * φ x)
            (fun _ : NPointDomain d n => bvt_W OS lgc n φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη
      ```

      Proof transcript: strengthen
      `SCV.tube_boundaryValueData_of_polyGrowth` to its compact-subcone
      uniform form, not merely its raywise form.  For fixed compact
      `tsupport φ` and compact `Kη`, the tube membership radius is uniform by
      compactness and `hKη_sub`; the OS-II polynomial growth bound from
      `full_analytic_continuation_with_acr_symmetry_growth` gives one
      integrable Schwartz seminorm bound independent of `η ∈ Kη` and small
      `ε`; continuity of the holomorphic integrand in `(ε,η,x)` gives local
      uniform convergence in `η`; a finite subcover of `Kη` upgrades raywise
      convergence to `TendstoUniformlyOn`.  After that, the OS45 common-chart
      theorems `os45_Hplus_commonBoundary_uniform` and
      `os45_Hminus_commonBoundary_uniform` are obtained by composing this
      compact-subcone theorem with the finite linear maps
      `os45CommonEdgeRealCLE`, `configPermCLE`, `os45CommonChartCLE`, and the
      branch-pullback identities.  This is an OS-II boundary-value transport
      step, not a locality or PET monodromy input.
   8. Apply `SCV.local_distributional_edge_of_the_wedge_envelope` after
      flattening the nested product by `flattenCLEquiv n (d + 1)` and
      `flattenCLEquivReal n (d + 1)`, then unflatten the output to get
      `Uc,Hc` in OS45 chart coordinates.
   9. Replace `Uc` by the connected component containing the nonempty common
      edge image.  Prove both selected trace families lie in this component
      through the plus/minus wedge paths supplied by the OS45 geometry.
   10. Finish the trace equations by rewriting:
      - the positive trace by the definition of `Hplus`,
        `Qρe.symm_apply_apply`, `BHW.permAct_wickRotatePoint`, and `τ`;
      - the negative trace by
        `BHW.os45PulledRealBranch_sub_eq_adjacentOS45RealEdgeDifference`.

Why this still does **not** finish Slot 1:

- at a Wick point one has
  `P_id(Q(z)) = bvt_F z` only when the chart point lies in the forward tube;
- similarly
  `P_swap(Q(z)) = bvt_F (permAct τ z)` only when the permuted Wick point also
  lies in the forward tube;
- the simultaneous forward-tube condition is a thin equal-time constraint, not
  the open agreement set required by a naive identity-theorem argument.

Therefore Slot 1 is not a naive forward-tube identity-theorem argument.  Its
proof must build the common OS45 EOW envelope directly from the local
common-boundary geometry, the Wick-side distributional equality supplied by
the OS-II/ACR-one witness, and the real-side branch-pullback support above.
It must not consume the downstream PET branch-independence theorem, because
that theorem itself now consumes the distributional Jost anchor produced from
this local data.

The branch-pullback support is genuine progress, but only as negative-side
chart infrastructure for that later common-boundary packaging.

Active decomposition of Slot 1:

1. build the local connected common-chart domain on which the adjacent Wick-side
   and real-side branch differences are both represented;
2. run the local distributional common-boundary / EOW step to produce the
   holomorphic common-chart branch-difference function `Hc`;
3. pull `Hc` back through the OS45 common-chart equivalence `Qρe`;
4. package the resulting direct-coordinate trace identities as
   `AdjacentOSEOWDifferenceEnvelope`.

Steps 3 and 4 are now checked in Lean as
`BHW.adjacentOSEOWDifferenceEnvelope_of_commonChartEnvelope`.  The live
mathematical work in Slot 1 is therefore exactly steps 1 and 2: prove the
common-chart OS45 distributional EOW supplier with the Wick and real trace
identities on the same selected patch `V`.

With that choice:

- the positive-side envelope trace is the honest direct Wick-side adjacent
  difference, whose vanishing is supplied downstream by
  `bvt_F_acrOne_package`;
- the negative-side envelope trace is the honest adjacent real-edge
  `extendF` difference;
- no tautological selected-branch cancellation appears anywhere in the active
  route;
- no local theorem slot is allowed to bypass the OS sequence
  symmetry -> continuation -> BHW -> Jost -> boundary locality.

The old "common-chart Wick difference" route is dead and should not be revived
in production code except as a cautionary note.

Implementation-readiness gate for the next Lean stage:

* Hard proof-doc gate for the local descent step: no further Lean
  implementation should proceed until the scalarized local quotient packet in
  `docs/scv_infrastructure_blueprint.md` is treated as the authoritative
  route transcript.  That packet now fixes the finite-seminorm decay theorem
  for `schwartzPartialEval₂CLM` down to the singleton source family
  `{(k,l), (k+N,l)}`, the finite-sup aggregation and empty-family case, the
  mixed real-fiber integral CLM derivative/decay theorem surfaces, the dense
  split-tensor reduction through the factored flat two-block Hermite theorem,
  the zero-dimensional tensor case, all parameter-test CLE signs and inverse
  formulas, the two scalar change-of-variables identities, the exact
  scalarized local quotient equality chain, and the final packaging proof for
  `translationCovariantProductKernel_descends_local`.  The Lean pass must
  follow those theorem names and proof dependencies literally; it must not
  invent a `SchwartzMap`-valued Bochner average, a global covariance quotient,
  or a new density/quotient axiom while filling this step.
  File ownership is also fixed: the next local descent implementation belongs
  in a companion file after `SCV/LocalProductDescent.lean` rather than growing
  that near-threshold substrate file.  The right mixed-fiber
  change-of-variables identity is the affine map `a ↦ t - a`; in Lean it is
  decomposed as `integral_neg_eq_self` followed by
  `integral_add_right_eq_self`, since `integral_sub_right_eq_self` alone has
  the opposite sign convention.
* Do **not** add another distributional EOW axiom or wrapper.  The checked SCV
  global recovery endpoint
  `SCV.regularizedEnvelope_chartEnvelope_from_productKernel` remains available
  only for a genuinely globally covariant product kernel.  The active
  pure-SCV theorem-2 route uses the local recovery consumer
  `SCV.regularizedEnvelope_chartEnvelope_from_localProductKernel`, because the
  cutoff-localized mixed functional constructed from a local fixed-window
  family satisfies only local covariance.
* The local continuous-EOW geometry supplier is now checked through
  `SCV.local_continuous_edge_of_the_wedge_envelope`; the fixed-kernel
  distributional-to-continuous bridge is checked as
  `SCV.regularizedLocalEOW_fixedKernelEnvelope_from_clm`; the fixed-window
  version needed for one coherent family is checked as
  `SCV.regularizedLocalEOW_fixedWindowEnvelope_from_clm`; and the explicit
  family package is checked as
  `SCV.regularizedLocalEOW_family_from_fixedWindow`.
* The old next-stage target
  `SCV.regularizedLocalEOW_productKernel_from_continuousEOW` is retired under
  its global-covariance surface.  The next QFT-free SCV stage is Lean
  implementation of the local descent package named below, in the exact order
  recorded in `docs/scv_infrastructure_blueprint.md`.  Its output must feed a
  local recovery consumer with `K`, `Gchart`, a local `Hdist`,
  `IsDistributionalHolomorphicOn Hdist Udesc`, local product-test descent, and
  the product-test representation on supported tests.  It must not claim
  `ProductKernelRealTranslationCovariantGlobal K`.
* Before proving the covariance field, use the checked
  `SCV/LocalEOWChartLinear.lean` transport API.  The real smoothing kernel must
  first be pushed from chart coordinates to the original real edge through
  `SCV.localEOWRealLinearKernelPushforwardCLM`; this is the surface that carries
  the inverse determinant factor and the checked support-radius transport.
  Then apply
  `SCV.realMollifyLocal_localEOWRealLinearKernelPushforwardCLM` to rewrite the
  side mollifier as the corresponding chart-coordinate integral before invoking
  fixed-window uniqueness/covariance.
* The immediate Lean-ready covariance support lemmas are the chart-local
  versions of that identity:
  `SCV.realMollifyLocal_localEOWChart_kernelPushforwardCLM`,
  `SCV.realMollifyLocal_localEOWChart_kernelPushforwardCLM_pullback`, and
  `SCV.realMollifyLocal_localEOWChart_translate_kernelPushforwardCLM`.  The
  pullback theorem is the direct side-agreement form
  `realMollifyLocal F (P φ) (localEOWChart x0 ys w) =
   realMollifyLocal (fun ζ => F (localEOWChart x0 ys ζ)) φ w`; the
  second theorem is the exact translated-kernel side-branch identity needed for
  the uniqueness proof of regularized-family covariance:
  pushing `translateSchwartz a φ` through the chart kernel and evaluating at
  `localEOWChart x0 ys w` is the same as pushing `φ` and evaluating at
  `localEOWChart x0 ys (w - realEmbed a)`.
* Route correction before the full product-kernel supplier: a local
  fixed-window family on `Metric.ball 0 (δ / 2)` does **not** by itself
  produce a globally translation-covariant mixed Schwartz functional
  `K : SchwartzMap (ComplexChartSpace m × (Fin m -> ℝ)) ℂ ->L[ℂ] ℂ`.
  Extending the local pairing
  `(φ, ψ) ↦ ∫ z, G ψ z * φ z` by a complex-chart cutoff would make a global
  functional, but the cutoff breaks
  `ProductKernelRealTranslationCovariantGlobal`.  Therefore the full theorem
  `SCV.regularizedLocalEOW_productKernel_from_continuousEOW` must not be
  implemented as a wrapper around the current local family plus an arbitrary
  extension.  The checked recovery theorem
  `SCV.regularizedEnvelope_chartEnvelope_from_productKernel` remains the right
  consumer once a genuinely global covariant `K` is available, or once a
  separately proved local-descent recovery theorem replaces the global
  covariance hypothesis.
* The recovery fork is now resolved for the pure-SCV theorem: use the local
  descent route, not an OS-specific global-`K` shortcut.  A genuinely global
  covariant kernel from OS/Wightman translation invariance may later shorten
  an OS-specialized proof, but it cannot be the construction of the QFT-free
  theorem `SCV.local_distributional_edge_of_the_wedge_envelope`.
* Checked local covariance substrate:
  `SCV.KernelSupportWithin.translateSchwartz`,
  `SCV.KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_translateSchwartz`,
  `SCV.localEOWShiftedWindow`,
  `SCV.isOpen_localEOWShiftedWindow`,
  `SCV.convex_localEOWShiftedWindow`,
  `SCV.isPreconnected_localEOWShiftedWindow`,
  `SCV.exists_positive_imag_mem_localEOWShiftedWindow_of_norm_lt`, and
  `SCV.regularizedLocalEOW_family_chartKernel_covariance_on_shiftedOverlap`.
* Implementation theorem surfaces for the local descent package:
  1. a localized mixed pairing CLM
     `regularizedLocalEOW_pairingCLM_of_fixedWindow`, built with nested
     complex-chart and real-kernel cutoffs that are equal to one on the support
     windows actually used;
  2. `regularizedLocalEOW_pairingCLM_localCovariant`, proving
     `ProductKernelRealTranslationCovariantLocal`, not global covariance, from
     the shifted-overlap covariance theorem and explicit support/margin
     hypotheses;
  3. `translationCovariantProductKernel_descends_local`, the local analogue of
     the checked sheared-product descent theorem.  It is not an invocation of
     the global arbitrary-test quotient and it does not use a
     `SchwartzMap`-valued averaging lemma.  It uses
     `shearedProductKernelFunctional_localQuotient_of_productCovariant`, a
     scalarized local fiber-integral quotient whose every covariance use is
     guarded by the local support window;
  4. `regularizedEnvelope_chartEnvelope_from_localProductKernel`, replacing
     the global product-kernel consumer by local `Hdist`, local
     `IsDistributionalHolomorphicOn`, local product-test descent, and the
     already checked pointwise-representation/delta-limit arguments.
  These four surfaces now have their hypotheses, support margins, and proof
  transcripts written out in `docs/scv_infrastructure_blueprint.md`; Lean
  should proceed with the helper extraction order there.  The complex-chart
  cutoff, SCV-local `schwartzPartialEval₁CLM` apply/tensor/seminorm package,
  compact `Lorig` value-CLM bound, chart-kernel value-CLM transport,
  chart-linear kernel pushforward API, and first varying-kernel continuity
  layer including the split moving-kernel side limits and bundled CLM boundary
  data are checked.  The newly exposed support helpers
  `norm_realEmbed_eq`,
  `SupportsInOpen.complexTranslateSchwartz_of_image_subset`,
  `regularizedEnvelope_productKernel_dbar_eq_zero_local`, and
  `translationCovariantKernel_distributionalHolomorphic_local` are also
  checked.  The pairing CLM and local covariance layer are now checked as
  `regularizedLocalEOW_pairingCLM_of_fixedWindow` and
  `regularizedLocalEOW_pairingCLM_localCovariant` in
  `SCV/LocalEOWPairingCLM.lean`.  The mixed-fiber change-of-variables and
  partial-evaluation identity layer is now checked in
  `SCV/LocalProductDescentIntegrals.lean`, and the same file now checks the
  scalarized local quotient and local product-test descent.  The local
  pointwise representation theorem
  `SCV.regularizedEnvelope_pointwiseRepresentation_of_localProductKernel` is
  now checked in `SCV/LocalProductRecovery.lean`, with `Udesc` as the
  representation/Fubini domain and `Ucov` only as the product-kernel
  representation domain.  The local chart-envelope recovery theorem
  `SCV.regularizedEnvelope_chartEnvelope_from_localProductKernel` is also
  checked in `SCV/LocalProductRecovery.lean`, using
  the explicit approximate-identity and side-agreement hypotheses.  Its
  consumer surface requires `IsOpen Udesc`, but not `IsOpen U0`, because `hCR`
  has already been proved on `Udesc` and `U0` is used only as the holomorphy
  window restricted through `Udesc ⊆ Ucov ⊆ U0`.  The partial-evaluation
  helper is proved in the SCV layer from
  `SchwartzMap.compCLM`; importing the Wightman partial-evaluation file would
  be route drift for this pure-SCV theorem.
* The next OS-side boundary-value theorem is
  `bvt_boundary_values_uniformOnCompactDirections` in
  `OSToWightmanBoundaryValuesBase.lean`.  It is not in the `BHW` namespace, and
  it must not be introduced as a new axiom.  It should be proved by upgrading
  the existing polynomial-growth boundary-value proof to compact direction
  sets, then specializing it to `bvt_F`.
* Only after those two inputs exist should the OS45 file introduce
  `BHW.os45_Hplus_commonBoundary_uniform`,
  `BHW.os45_Hminus_commonBoundary_uniform`, and finally
  `BHW.os45_adjacent_commonBoundaryEnvelope`.

Current implementation order:

1. finish the pure-SCV theorem package needed by Slot 1, reading the checked
   declaration ledger literally.  The checked substrate is now:
   `SCV.complexTranslateSchwartz`, `SCV.schwartzTensorProduct₂`,
   `SCV.realConvolutionTest`,
   `SCV.translationCovariantProductKernel_descends`,
   `SCV.distributionalHolomorphic_regular`,
   `SCV.localEOWCoefficientSimplex`,
   `SCV.localEOWSimplexDirections`,
   `SCV.isCompact_localEOWCoefficientSimplex`,
   `SCV.isCompact_localEOWSimplexDirections`,
   `SCV.localEOWRealChart`,
   `SCV.localEOWChart`,
   `SCV.localEOWRealLinearPart`,
   `SCV.localEOWRealChart_eq_x0_add_linearPart`,
   `SCV.localEOWRealChart_sub`,
   `SCV.localEOWRealChart_add`,
   `SCV.localEOWChart_sub_realEmbed`,
   `SCV.localEOWChart_add_realEmbed`,
   `SCV.localEOWRealLinearMatrix`,
   `SCV.localEOWRealLinearMatrix_mulVec`,
   `SCV.localEOWRealLinearCLE`,
   `SCV.localEOWRealLinearCLE_apply`,
   `SCV.localEOWRealLinearPullbackCLM`,
   `SCV.localEOWRealLinearPullbackCLM_apply`,
   `SCV.KernelSupportWithin.localEOWRealLinearPullbackCLM`,
   `SCV.continuous_localEOWRealChart`,
   `SCV.localEOWChart_zero`,
   `SCV.differentiable_localEOWChart`,
   `SCV.continuous_localEOWChart`,
   `SCV.localEOWChart_im`,
   `SCV.localEOWChart_real`,
   `SCV.localEOWChart_conj`,
   `SCV.localEOWChart_affine_real_combo`,
   `SCV.localEOWChart_inverse_conj`,
   `SCV.localEOWChart_equiv`,
   `SCV.localEOWChart_inverse_ball_geometry`,
   `SCV.isCompact_localEOWRealChart_image`,
   `SCV.localEOWRealChart_closedBall_subset`,
   `SCV.localEOW_closedBall_support_margin`,
   `SCV.localEOWSmp`,
   `SCV.localEOWSmp_zero`,
   `SCV.localEOWSmp_im_pos_of_real`,
   `SCV.localEOWSmp_im_neg_of_real`,
   `SCV.localEOWSmp_norm_le_extended`,
   `SCV.localEOWSmp_norm_le_extended_of_closedBall`,
   `SCV.localEOWSmp_div_norm_lt_one_of_closedBall`,
   `SCV.localEOWSmp_im_zero_of_unit_real`,
   `SCV.localEOWChart_smp_realEdge_eq_of_unit_real`,
   `SCV.continuous_localEOWSmp_theta`,
   `SCV.localEOWSmp_im_zero_of_real`,
   `SCV.localEOWChart_smp_realEdge_eq_of_real`,
   `SCV.continuousAt_localEOWSmp_of_norm_lt_two`,
   `SCV.continuousAt_localEOWChart_smp_of_norm_lt_two`,
   `SCV.differentiableAt_localEOWSmp_of_real`,
   `SCV.differentiableAt_localEOWChart_smp_of_real`,
   `SCV.differentiableOn_localEOWChart_smp_upperHalfPlane_of_real`,
   `SCV.differentiableOn_localEOWChart_smp_lowerHalfPlane_of_real`,
   `SCV.tendsto_localEOWChart_smp_upperHalfPlane_to_realEdge`,
   `SCV.tendsto_localEOWChart_smp_lowerHalfPlane_to_realEdge`,
   `SCV.continuousAt_localEOWRealChart_smp_re_of_norm_lt_two`,
   `SCV.continuousAt_localEOWBoundaryValue_smp`,
   `SCV.differentiableOn_localEOWUpperBranch_smp_of_real`,
   `SCV.differentiableOn_localEOWLowerBranch_smp_of_real`,
   `SCV.tendsto_localEOWUpperBranch_smp_to_boundaryValue`,
   `SCV.tendsto_localEOWLowerBranch_smp_to_boundaryValue`,
   `SCV.local_rudin_mean_value_real`,
   `SCV.continuousAt_localEOWSmp_param`,
   `SCV.exists_localRudin_coordinate_update_margin`,
   `SCV.differentiableAt_localRudin_parametric_integral`,
   `SCV.exists_localContinuousEOW_chart_window`,
   `SCV.localEOWChart_ball_positive_mem_of_delta`,
   `SCV.localEOWChart_ball_negative_mem_of_delta`,
   `SCV.localEOWChart_smp_upper_mem_of_delta_on_sphere`,
   `SCV.localEOWChart_smp_lower_mem_of_delta_on_sphere`,
   `SCV.localRudinIntegrand`,
   `SCV.localRudinIntegral`,
   `SCV.localRudinEnvelope`,
   `SCV.aestronglyMeasurable_localRudinIntegrand`,
   `SCV.continuousAt_localRudinIntegrand_param`,
   `SCV.continuousAt_localRudinIntegral_of_bound`,
   `SCV.differentiableAt_localRudinIntegrand_update`,
   `SCV.localRudinIntegrand_zero_of_sin_eq_zero`,
   `SCV.differentiableAt_localRudinIntegral_of_bound`,
   `SCV.differentiableOn_localRudinIntegral_of_bound`,
   `SCV.differentiableOn_localRudinEnvelope_of_bound`,
   `SCV.exists_bound_localRudinIntegrand`,
   `SCV.differentiableOn_localRudinEnvelope`,
   `SCV.localRudinEnvelope_eq_boundary_of_real`,
   `SCV.localEOWLine`,
   `SCV.localEOWLine_I`,
   `SCV.localEOWLine_im`,
   `SCV.localEOWLine_real_im_zero`,
   `SCV.differentiable_localEOWLine`,
   `SCV.localEOWLine_zero_mem_ball`,
   `SCV.localEOWLine_norm_le_delta_ten_of_norm_le_two`,
   `SCV.localEOWLine_re_closedBall_of_norm_le_two`,
   `SCV.localEOWChart_line_upper_mem_of_delta`,
   `SCV.localEOWChart_line_lower_mem_of_delta`,
   `SCV.localEOWChart_line_upper_mem_of_delta_of_negative`,
   `SCV.localEOWChart_line_lower_mem_of_delta_of_negative`,
   `SCV.localEOWLine_affine_real_combo`,
   `SCV.localEOWLine_chart_real`,
   `SCV.tendsto_localEOWLine_upper_to_boundaryValue`,
   `SCV.tendsto_localEOWLine_lower_to_boundaryValue`,
   `SCV.tendsto_localEOWLine_upper_to_boundaryValue_of_negative`,
   `SCV.tendsto_localEOWLine_lower_to_boundaryValue_of_negative`,
   `SCV.localRudinEnvelope_line_eq_boundary_of_real`,
   `SCV.localRudinEnvelope_eq_plus_on_positive_ball`,
   `SCV.localRudinEnvelope_eq_minus_on_negative_ball`,
   `SCV.localEOWSmp_re_mem_closedBall`,
   `SCV.exists_localEOWSmp_delta`,
   `SCV.localEOWChart_smp_upper_mem_of_delta`,
   `SCV.localEOWChart_smp_lower_mem_of_delta`,
   `SCV.exists_localEOWChart_smp_delta`,
   `SCV.localEOWChart_real_imag`,
   `SCV.localEOWSimplexDirections_subset_cone`,
   `SCV.localEOW_positive_imag_normalized_mem_simplex`,
   `SCV.localEOW_chart_positive_polywedge_mem`,
   `SCV.localEOW_chart_negative_polywedge_mem`,
   `SCV.localEOW_chart_twoSided_polywedge_mem`,
   `SCV.localEOWChart_twoSided_polywedge_mem`,
   `SCV.local_edge_of_the_wedge_1d`,
   `SCV.KernelSupportWithin.add`,
   `SCV.KernelSupportWithin.smul`,
   `SCV.KernelSupportWithin.smulLeftCLM`,
   `SCV.KernelSupportWithin.smulLeftCLM_of_leftSupport`,
   `SCV.KernelSupportWithin.smulLeftCLM_eq_of_eq_one_on_closedBall`,
   `SCV.exists_schwartz_cutoff_eq_one_on_closedBall`,
   `SCV.exists_closedBall_integral_clm_of_continuousOn`,
   `SCV.realMollifyLocal_eq_sliceIntegral_translate`,
   `SCV.realMollifyLocal_eq_sliceFunctional`,
   `SCV.exists_cutoffSliceIntegral_clm_of_continuousOn`,
   `SCV.realMollifyLocal_eq_cutoffSliceCLM`,
   `SCV.tendsto_cutoffSliceCLM_of_boundaryValue`,
   `SCV.exists_cutoffSliceCLM_family_of_boundaryValue`,
   `SCV.zero_not_mem_localEOWSimplexDirections`,
   `SCV.tendsto_neg_nhdsWithin_zero_neg_image`,
   `SCV.exists_realMollifyLocal_valueCLM_of_closedBall`,
   `SCV.exists_bound_realMollifyLocal_smulLeftCLM`,
   `SCV.exists_bound_localRudinEnvelope_smulLeftCLM_of_side_bounds`,
   `SCV.exists_schwartz_bound_normalized_intervalIntegral_clm_family`,
   `SCV.exists_localRudinIntegrand_smulLeftCLM_clmFamily`,
   `SCV.exists_schwartz_bound_localRudinEnvelope_smulLeftCLM_value`,
   `SCV.regularizedEnvelope_valueCLM_of_cutoff`,
   `SCV.integrable_realMollifyLocal_integrand_of_translate_margin`,
   `SCV.localRealMollifySide_holomorphicOn_of_translate_margin`,
   `SCV.localRealMollify_commonContinuousBoundary_of_clm`,
   `SCV.realMollifyLocal_translateSchwartz`,
   `SCV.realMollifyLocal_add_of_integrable`,
   `SCV.realMollifyLocal_add_of_translate_margin`,
   `SCV.realMollifyLocal_smul`,
   `SCV.regularizedLocalEOW_fixedKernelEnvelope_from_clm`,
   `SCV.regularizedLocalEOW_fixedWindowEnvelope_from_clm`,
   `SCV.regularizedLocalEOW_family_from_fixedWindow`,
   `SCV.regularizedLocalEOW_family_add`,
   `SCV.regularizedLocalEOW_family_smul`,
   `SCV.exists_seminorm_bound_complexRealFiberIntegralRaw_zero`,
   `SCV.basePrecompCLM`,
   `SCV.baseFDerivSchwartzCLM`,
   `SCV.exists_seminorm_bound_baseFDerivSchwartz`,
   `SCV.exists_seminorm_bound_complexRealFiberIntegralRaw_deriv`,
   `SCV.complexRealFiberIntegralCLM`,
   `SCV.complexRealFiberIntegralCLM_apply`,
   `SCV.boundaryProductKernel_from_fiberIntegralCLM`,
   `SCV.boundaryProductKernel_from_complexRealFiberIntegralCLM`,
   `SCV.regularizedEnvelope_productKernel_dbar_eq_zero`,
   `SCV.translationCovariantKernel_distributionalHolomorphic`,
   `SCV.regularizedEnvelope_holomorphicDistribution_from_productKernel`,
   `SCV.regularizedEnvelope_pointwiseRepresentation_of_productKernel`,
   `SCV.regularizedEnvelope_deltaLimit_agreesOnWedges`, and
   `SCV.regularizedEnvelope_chartEnvelope_from_productKernel`, and
   `SCV.local_continuous_edge_of_the_wedge_envelope`.  The local-descent and
   varying-kernel checked additions also include
   `SCV.exists_bound_localRudinIntegrand_varyingKernel`,
   `SCV.continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand`,
   `SCV.norm_realEmbed_eq`,
   `SCV.tsupport_subset_preimage_tsupport_complexTranslateSchwartz`,
   `SCV.integral_mul_complexTranslateSchwartz_eq_shift_of_support`,
   `SCV.regularizedLocalEOW_pairingCLM_of_fixedWindow`,
   `SCV.regularizedLocalEOW_pairingCLM_localCovariant`,
   `SCV.SupportsInOpen.complexTranslateSchwartz_of_image_subset`,
   `SCV.realEmbedContinuousLinearMap`,
   `SCV.realEmbedContinuousLinearMap_apply`,
   `SCV.schwartzTensorProduct₂CLMLeft`,
   `SCV.schwartzTensorProduct₂CLMLeft_apply`,
   `SCV.schwartzTensorProduct₂CLMLeft_eq`,
   `SCV.schwartzPartialEval₂CLM`,
   `SCV.schwartzPartialEval₂CLM_apply`,
   `SCV.continuous_schwartzPartialEval₂CLM`,
   `SCV.schwartzPartialEval₂CLM_seminorm_decay_one`,
   `SCV.schwartzPartialEval₂CLM_finsetSeminorm_decay`,
   `SCV.exists_schwartzFunctional_finsetSeminormBound`,
   `SCV.integrable_apply_schwartzPartialEval₂CLM`,
   `SCV.exists_bound_apply_schwartzPartialEval₂CLM_integral`,
   `SCV.mixedRealFiberIntegralRaw`,
   `SCV.integrable_mixedRealFiber`,
   `SCV.mixedBaseFDerivSchwartz`,
   `SCV.hasFDerivAt_mixedRealFiberIntegralRaw`,
   `SCV.fderiv_mixedRealFiberIntegralRaw_eq`,
   `SCV.contDiff_mixedRealFiberIntegralRaw`,
   `SCV.decay_mixedRealFiberIntegralRaw`,
   `SCV.exists_seminorm_bound_mixedRealFiberIntegralRaw_zero`,
   `SCV.mixedBasePrecompCLM`,
   `SCV.mixedBaseFDerivSchwartzCLM`,
   `SCV.exists_seminorm_bound_mixedBaseFDerivSchwartz`,
   `SCV.exists_seminorm_bound_mixedRealFiberIntegralRaw_deriv`,
   `SCV.mixedRealFiberIntegralCLM`,
   `SCV.mixedRealFiberIntegralCLM_apply`,
   `SCV.mixedBaseFiberTensor`,
   `SCV.mixedBaseFiberTensor_apply`,
   `SCV.schwartzPartialEval₂CLM_mixedBaseFiberTensor`,
   `SCV.mixedRealFiberIntegralCLM_mixedBaseFiberTensor`,
   `SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts_of_pos`,
   `SCV.flatTwoBlockProductDense_of_pos`,
   `SCV.mixedBaseFlatCLE`,
   `SCV.mixedBaseFlatCLE_apply`,
   `SCV.mixedBaseFiberFlatCLE`,
   `SCV.mixedBaseFiberFlatCLE_apply`,
   `SCV.mixedBaseFiberFlatCLE_symm_append`,
   `SCV.flatTwoBlockProduct_eq_mixedBaseFiberTensor`,
   `SCV.mixedBaseFiberCLM_zero_of_zero_on_tensors`,
   `SCV.mixedBaseFiberProductTensorDense_zero`,
   `SCV.mixedBaseFiberProductTensorDense_of_pos`,
   `SCV.mixedBaseFiberProductTensorDense_all`,
   `SCV.mixedRealFiberIntegralScalarCLM`,
   `SCV.mixedRealFiberIntegralScalarCLM_apply`,
   `SCV.mixedRealFiberIntegralScalarCLM_eq_comp_mixedRealFiberIntegralCLM`,
   `SCV.continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral`,
   `SCV.realParamKernelLeftCLE`,
   `SCV.realParamKernelLeftCLE_apply`,
   `SCV.realParamKernelLeftCLE_symm_apply`,
   `SCV.realParamKernelLeft`,
   `SCV.realParamKernelLeft_apply`,
   `SCV.realParamKernelRightCLE`,
   `SCV.realParamKernelRightCLE_apply`,
   `SCV.realParamKernelRightCLE_symm_apply`,
   `SCV.realParamKernelRight`,
   `SCV.realParamKernelRight_apply`,
   `SCV.localDescentParamTestLeftCLE`,
   `SCV.localDescentParamTestLeftCLE_apply`,
   `SCV.localDescentParamTestLeftCLE_symm_apply`,
   `SCV.localDescentParamTestLeft`,
   `SCV.localDescentParamTestLeft_apply`,
   `SCV.localDescentParamTestRightCLE`,
   `SCV.localDescentParamTestRightCLE_apply`,
   `SCV.localDescentParamTestRightCLE_symm_apply`,
   `SCV.localDescentParamTestRight`,
   `SCV.localDescentParamTestRight_apply`,
   `SCV.mixedRealFiberIntegralCLM_localDescentParamTestLeft`,
   `SCV.mixedRealFiberIntegralCLM_localDescentParamTestRight`,
   `SCV.schwartzPartialEval₂CLM_localDescentParamTestLeft`,
   `SCV.translateSchwartz_neg_smulLeft_eta_translate`,
   `SCV.schwartzPartialEval₂CLM_localDescentParamTestRight`,
   `SCV.shearedProductKernelFunctional_localQuotient_of_productCovariant`,
   `SCV.translationCovariantProductKernel_descends_local`,
   `SCV.regularizedEnvelope_pointwiseRepresentation_of_localProductKernel`,
   `SCV.regularizedEnvelope_chartEnvelope_from_localProductKernel`,
   `SCV.regularizedEnvelope_productKernel_dbar_eq_zero_local`, and
   `SCV.translationCovariantKernel_distributionalHolomorphic_local`.
   The local covariant product-kernel assembly
   `SCV.regularizedEnvelope_chartEnvelope_from_localCovariantProductKernel` is
   now checked in `SCV/LocalProductRecovery.lean`.  The remaining pure-SCV
   declaration is
   `SCV.local_distributional_edge_of_the_wedge_envelope`.  The retired
   `SCV.regularizedLocalEOW_productKernel_from_continuousEOW` name may only be
   reused later as an assembly wrapper around those local theorems, not as a
   global-covariance supplier.  Older placeholder
   names such as `SCV.localRealMollify_commonContinuousBoundary`,
   `SCV.regularizedLocalEOW_family`,
   `SCV.regularizedEnvelope_linearContinuousInKernel`,
   `SCV.regularizedEnvelope_translationCovariant`,
   `SCV.regularizedEnvelope_productKernel`, and
   `SCV.regularizedEnvelope_kernelRepresentation` must not be cited as current
   Lean API unless they are introduced as proved theorem names.  These are pure
   SCV / topological-vector-space theorem surfaces and must not import Wightman
   or OS files.
   `SCV.complexTranslateSchwartz`, `SCV.schwartzTensorProduct₂`,
   `SCV.realConvolutionShearCLE`, `SCV.complexRealFiberIntegralRaw`, and
   `SCV.integrable_complexRealFiber`, plus `SCV.baseFDerivSchwartz` and
   `SCV.exists_norm_pow_mul_complexRealFiberIntegralRaw_le` and
   `SCV.exists_integrable_bound_baseFDerivSchwartz` and
   `SCV.hasFDerivAt_complexRealFiberIntegralRaw`, plus the raw integral
   smoothness and decay theorems, `SCV.complexRealFiberIntegral`, and
   `SCV.realConvolutionTest` with the exact convolution test formula
   `realConvolutionTest φ ψ z = ∫ t, φ (z - realEmbed t) * ψ t`,
   and the translation identity
   `realConvolutionTest (complexTranslateSchwartz a φ) ψ =
    realConvolutionTest φ (translateSchwartz a ψ)`, are now checked in
   `SCV/DistributionalEOWKernel.lean`.  The same file now also checks the
   first fiber-descent primitives:
   `SCV.complexRealFiberTranslateSchwartzCLM`,
   `SCV.complexRealFiberIntegral_fiberTranslate`,
   `SCV.complexRealFiberIntegral_schwartzTensorProduct₂`,
   `SCV.translateSchwartz_translateSchwartz`,
   `SCV.complexTranslateSchwartz_complexTranslateSchwartz`,
   `SCV.shearedProductKernelFunctional`, and
   `SCV.IsComplexRealFiberTranslationInvariant`, plus the sheared tensor
   identity `SCV.complexRealFiberTranslate_shearedTensor_eq`.  The mixed
   fiber quotient and its normalized-cutoff consumer are now checked:
   `SCV.map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant`,
   `SCV.schwartzTensorProduct₂CLMRight`,
   `SCV.complexRealFiberTranslationDescentCLM`, and
   `SCV.map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant`.
   The product-density/descent layer is now checked as well:
   `SCV.shearedProductKernel_fiberTranslate_shearedTensor_eq_self_of_productCovariant`,
   `SCV.shearedProductKernel_fiberInvariant_of_productCovariant_of_shearedProductTensorDense`,
   `SCV.translationCovariantProductKernel_descends_of_shearedProductTensorDense`,
   `SCV.translationCovariantProductKernel_descends_of_productTensorDense`,
   `SCV.ProductTensorDense_all`, and
   `SCV.translationCovariantProductKernel_descends`.  The
   product-kernel `∂bar` consumer, distributional-holomorphicity continuity
   passage, and compact approximate-identity construction are also checked via
   `SCV.regularizedEnvelope_productKernel_dbar_eq_zero`,
   `SCV.translationCovariantKernel_distributionalHolomorphic`,
   `SCV.tendsto_realConvolutionTest_of_shrinking_normalized_support`, and
   `SCV.exists_realConvolutionTest_approxIdentity`.  The first
   `SCV.distributionalHolomorphic_regular` calculus layer is also checked in
   `SCV/DistributionalEOWRegularity.lean`: `dzSchwartzCLM`, support
   preservation, real-direction commutation, the coordinate-Laplacian identity
   `SCV.complexChartLaplacianSchwartzCLM_eq_four_sum_dbar_dz`, and
   `SCV.local_laplacian_zero_of_distributionalHolomorphic`, plus the
   `SCV.pointwiseDbar` definition and
   `SCV.dbarSchwartzCLM_apply_eq_pointwiseDbar` bridge.  The first Euclidean
   transport objects, coordinate-direction transport lemmas, Euclidean
   coordinate Laplacian comparison, chart-Laplacian transport theorem,
   transported distribution, support transport in both directions,
   volume-preserving chart-change theorem, and Euclidean-representative
   pullback theorem are checked as well.  The first pure Euclidean
   moving-kernel layer for the Weyl route, including reflected translate support
   control, derivative commutation, first-order translation seminorm estimates,
   the pointwise quotient-derivative identity, compact-kernel continuity,
   Schwartz-topology difference-quotient convergence, and the one-parameter
   derivative theorem for reflected regularizations, is checked in
   `SCV/EuclideanWeyl.lean`.  The direction-uniform Fréchet remainder ladder is
   now checked in `SCV/EuclideanWeylFrechet.lean` through
   `hasFDerivAt_regularizedDistribution` and
   `contDiff_regularizedDistribution`.  The proof slot is recorded in
   `docs/scv_infrastructure_blueprint.md`: build
   `exists_seminorm_secondLineDeriv_unit_bound` from
   `LineDeriv.bilinearLineDerivTwo ℝ φ`, `EuclideanSpace.basisFun ι ℝ`,
   `EuclideanSpace.norm_sq_eq`, `Finset.single_le_sum`, and the seminorm
   finite-sum triangle inequality, promote it to uniform translated and
   quadratic remainders, then compose the Schwartz-topology limit with the
   reflected functional and close smoothness by finite-order induction.  The
   first normalized Euclidean bump substrate is now checked in
   `SCV/EuclideanWeylBump.lean`: normalized compact radial bumps, real-valued
   nonnegativity, support in `closedBall 0 ε`, and zero integral/compact
   support for differences.  The profile-scaling weighted-mass subpackage is
   now also checked: the real raw integral scales by Euclidean Haar scaling, the
   one-variable weighted raw mass scales by the same power, and the normalized
   weighted mass is independent of the radius.  The bump-subprofile support,
   plateau, and norm-equality facts are checked as well.  The first
   finite-interval radial Poisson substrate is now checked in
   `SCV/EuclideanWeylPoisson.lean`: the radial mass and primitive definitions,
   the FTC derivative of the radial mass, the global weighted-mass bridge from
   the checked `Ioi` mass to the finite ODE boundary condition, the near-zero
   constant-mass formula, the linear primitive-derivative formula, and the
   quadratic primitive profile at the origin, the away-from-zero radial ODE,
   the positive-radius scalar profile-Laplacian theorem, primitive vanishing
   outside the support radius, and the Euclidean origin smoothness/Laplacian
   calculation from the quadratic norm germ.  The off-origin norm geometry is
   now checked through the finite-sum identities, norm Hessian, coordinate
   quotient derivative, local `ContDiffAt` neighborhood rewrite of the first
   derivative of `a ∘ ‖·‖`, radial second-chain-rule product body, summed
   off-origin profile Laplacian, positive-half-line smoothness for the
	   primitive profile, the all-points Poisson theorem
	   `laplacian_radialPrimitiveProfile`, compact support and exact
	   topological-support radius for the norm-composed primitive, Schwartz
	   packaging, the positive-dimensional bump-difference primitive theorem
	   `exists_compact_laplacian_eq_euclideanWeylBump_sub_with_support`,
	   reflected-translate Laplacian commutation, and the harmonic bump
	   scale-invariance theorem `regularizedDistribution_bump_scale_eq`.  The
	   local ball-representative layer is now checked in
	   `SCV/EuclideanWeylRegularity.lean`: the margin support lemmas,
	   `euclideanWeylBallRepresentative`, fixed-regularization equality on
	   smaller balls, `contDiffOn_euclideanWeylBallRepresentative`, and the
	   checked Mathlib-convolution surface
	   `euclideanConvolutionTest_apply_reflectedTranslate`.  The next genuine
	   SCV substrate target remains the localized Euclidean Weyl theorem itself,
	   now at the scalar distribution-pairing identity plus compact-support
	   approximate-identity representation assembly.  The pairing route is the
	   finite-probe/ordinary-Bochner route recorded in
	   `docs/scv_infrastructure_blueprint.md`, matching the
	   Streater-Wightman regularization identity and avoiding any
	   `SchwartzMap`-valued Bochner shortcut.  That SCV blueprint now fixes the
	   first Lean implementation packet exactly, and
	   `SCV/EuclideanWeylProbe.lean` checks it: Euclidean polynomial weights,
	   coordinate iterated line-derivative CLMs, weighted bounded-continuous
	   probes, `euclideanProbeCLM`, and the finite-dimensional
	   coordinate-domination theorem required before the Hahn-Banach
	   factorization.  The Hahn-Banach factorization through the checked probe
	   map is now also checked as
	   `SCV.euclideanSchwartzFunctional_exists_probe_factorization`; it does not
	   add an axiom or a theorem-level `sorry`.  The componentwise
	   Banach-valued probe integral identity and the compact-kernel scalar
	   pairing theorem are now checked in `SCV/EuclideanWeylPairing.lean` as
	   `integral_euclideanPairingProbeFamily_eq_probe_convolution` and
	   `regularizedDistribution_integral_pairing`; these are the ordinary
	   Bochner replacement after finite factorization.  The Euclidean
	   approximate-identity theorem is now checked in
	   `SCV/EuclideanWeylApproxIdentity.lean` through
	   `tendsto_euclideanConvolutionTest_of_shrinking_normalized_support` and
	   `exists_euclideanConvolutionTest_approxIdentity`; it proves convergence
	   in the full Schwartz topology from explicit normalized compact Weyl
	   bumps.  The smaller-ball representation theorem is now checked in
	   `SCV/EuclideanWeylRepresentation.lean` as
	   `euclidean_laplacian_distribution_regular_on_ball`; it combines
	   scale-invariance, scalar pairing, and approximate identity to represent
	   the harmonic distribution on `Metric.ball c r`.  The next implementation
	   stage is the open-set representation assembly, now pinned in
	   `docs/scv_infrastructure_blueprint.md` as a canonical ball-representative
	   patching argument plus finite smooth partitions only on compact test
	   supports.  The representative is the pointwise canonical Weyl ball
	   representative with a radius chosen from openness; local equality to a
	   fixed ball representative supplies smoothness.  The first prerequisites are now checked in
	   `SCV/EuclideanWeylOpen.lean`: radius selection inside an open set,
	   the canonical open representative, local equality to fixed ball
	   representatives, smoothness on the open set, support preservation for
	   `χ * φ`, finite compact smooth partitions converted to Schwartz maps,
	   finite partition decomposition of a compactly supported Schwartz test,
	   and local compact-support integrability for `Hloc * (χ * φ)`.
	   `SCV/EuclideanWeylRepresentation.lean` also now exposes the
	   non-existential theorem
	   `euclideanWeylBallRepresentative_represents_on_ball`.  The finite
	   summation identity and the full open-set theorem
	   `euclidean_weyl_laplacian_distribution_regular_on_open` are now checked
	   in `SCV/EuclideanWeylOpen.lean`.  The downstream complex-chart theorem
	   `SCV.distributionalHolomorphic_regular` is now checked in
	   `SCV/DistributionalEOWHolomorphic.lean`: Euclidean Weyl is transported
	   through `complexChartEuclideanCLE`, distributional `∂bar = 0` is
	   extracted to pointwise `pointwiseDbar = 0` by the local fundamental lemma
	   and cutoff representative, and finite-dimensional CR linear algebra gives
	   the complex derivative witness.  The next local SCV targets are therefore
	   regularized-envelope recovery, local continuous EOW extraction, and
	   patching, all as recorded in `docs/scv_infrastructure_blueprint.md`.
	   The immediate checked bridge is now
	   `SCV.regularizedEnvelope_holomorphicDistribution_from_productKernel`,
	   which assembles product-kernel descent, compact approximate identities,
	   the product-kernel `∂bar` consumer, and
	   `SCV.distributionalHolomorphic_regular`.  The downstream delta-limit
	   agreement is now checked as well: shrinking-support geometry,
	   compact-support integrability, the representation-to-difference identity,
	   `SCV.regularizedEnvelope_kernelLimit_from_representation`, and
	   `SCV.regularizedEnvelope_deltaLimit_agreesOnWedges` are all in
	   `SCV/DistributionalEOWKernelRecovery.lean`.  The pointwise
	   representation bridge is also checked there:
	   `SCV.realConvolutionTest_supportsInOpen_of_translate_margin` supplies
	   the support obligation, `SCV.continuousOn_realMollifyLocal_of_translate_margin`
	   supplies mollifier continuity,
	   `SCV.realConvolutionTest_pairing_eq_mollifier_pairing` supplies the
	   compact-support Fubini/change-of-variables identity, and
	   `SCV.regularizedEnvelope_pointwise_eq_of_test_integral_eq` supplies the
	   final test-pairing-to-pointwise step.  The checked
	   `SCV.regularizedEnvelope_pointwiseRepresentation_of_productKernel`
	   combines those ingredients, and the checked final assembly theorem
	   `SCV.regularizedEnvelope_chartEnvelope_from_productKernel` combines it
	   with kernel recovery and delta-limit wedge agreement.  The remaining
	   theorem-2 SCV frontier is therefore upstream: extract the local
	   continuous EOW construction, prove the regularized local EOW family,
	   prove its linearity/continuity and real-translation covariance, and
	   package the actual product kernel `K` plus `G,hcov,hG_holo,hK_rep` for
	   the checked chart-assembly theorem.
	   The tensor-level sign bridge before
   the density step remains explicit:
   `SCV.shearedProductKernel_fiberTranslate_shearedTensor_eq_self_of_productCovariant`
   proves invariance on each sheared product tensor by applying
   `SCV.ProductKernelRealTranslationCovariantGlobal` at `-a` and simplifying
   `translateSchwartz (-a) (translateSchwartz a ψ)` to `ψ`.  This is the
   correct intermediate theorem: it proves the OS-II covariance calculation on
   generators.  The promotion theorem itself retains the
   explicit hypothesis `SCV.ShearedProductTensorDense m`: from that dense-span
   hypothesis, `Submodule.span_induction` plus closedness of the equalizer of
   two continuous linear maps gives
   `SCV.shearedProductKernel_fiberInvariant_of_productCovariant_of_shearedProductTensorDense`.
   The checked normalized fiber quotient then yields
   `SCV.translationCovariantProductKernel_descends_of_shearedProductTensorDense`,
   with the descended distribution
   `SCV.complexRealFiberTranslationDescentCLM
     (SCV.shearedProductKernelFunctional K) η`.
   The conditional dense-span promotion and descent are now checked in
   `SCV/DistributionalEOWProductKernel.lean`, and the unqualified descent
   theorem is discharged by the checked product-density theorem.
   The next product-kernel reduction is now checked: introduce the
   unsheared generator family
   `SCV.productTensorSet m = {schwartzTensorProduct₂ φ ψ}`, its span
   `SCV.productTensorSpan m`, and the standard density hypothesis
   `SCV.ProductTensorDense m`.  Prove
   `SCV.shearedProductTensorSet_eq_image_productTensorSet` and
   `SCV.shearedProductTensorSpan_eq_productTensorSpan_map` using the checked
   shear map
   `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
     (SCV.realConvolutionShearCLE m)` and `Submodule.map_span`.  Then prove
   `SCV.shearedProductTensorDense_of_productTensorDense` by transporting
   topological closure along the surjective shear CLM:
   convert both density statements with
   `Submodule.dense_iff_topologicalClosure_eq_top`, obtain surjectivity from
   `SCV.compCLMOfContinuousLinearEquiv_symm_left_inv`, and apply
   `DenseRange.topologicalClosure_map_submodule`.  The corollary
   `SCV.translationCovariantProductKernel_descends_of_productTensorDense`
   is the theorem-2 consumer surface for this stage.
   The proof of `SCV.ProductTensorDense m` is now routed through pure
   SCV/GaussianField infrastructure:
   flatten the mixed chart by `SCV.mixedChartFiberFirstCLE m`, use the checked
   `SCV.schwartzExternalProduct` to define `SCV.twoBlockProductSchwartz`, prove
   that flat two-block products pull back to `SCV.schwartzTensorProduct₂`, use
   `GaussianField.productHermite_schwartz_dense (D := ℝ) (m + m*2)` for
   `0 < m`, and split one-dimensional Hermite products into the first `m`
   fiber coordinates and the last `m*2` flattened complex-chart coordinates.
   Complex-valued tests are recovered from real-valued density by the local
   pure-SCV decomposition
   `SCV.complexSchwartzDecomposeCLE :
     SchwartzMap D ℂ ≃L[ℝ] (SchwartzMap D ℝ × SchwartzMap D ℝ)`.
   The final density theorem uses the same Hahn-Banach separation transcript as
   `Wightman/Reconstruction/DenseCLM.lean`, replacing Wightman nuclear
   uniqueness by the new mixed-product CLM uniqueness theorem.  The `m = 0`
   base case is a direct singleton-domain span calculation.  This route is now
   checked in `OSReconstruction/SCV/ProductDensity.lean`; the Lean targets
   discharged there are `SCV.flatTwoBlockProduct_eq_mixedProduct`,
   `SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts`,
   `SCV.mixedProductCLM_zero_of_zero_on_productTensor`,
   `SCV.ProductTensorDense_of_pos`, `SCV.ProductTensorDense_zero`, and
   `SCV.ProductTensorDense_all`, culminating in
   `SCV.translationCovariantProductKernel_descends`.
   The mixed-base density step is now checked too.  It reuses that proof
   without adding any new density assumption: the positive flat theorem is
   factored as `SCV.flatComplexCLM_zero_of_zero_on_twoBlockProducts_of_pos`
   and `SCV.flatTwoBlockProductDense_of_pos`, then transported through the
   Lean-facing equivalences `SCV.mixedBaseFlatCLE` and
   `SCV.mixedBaseFiberFlatCLE`.  The `m = 0` branch of
   `SCV.mixedBaseFiberProductTensorDense_all` is a direct singleton-constant
   calculation, not a generic zero-block flat theorem.
   The scalarized mixed real-fiber integral is also now checked:
   `SCV.integrable_apply_schwartzPartialEval₂CLM` and
   `SCV.exists_bound_apply_schwartzPartialEval₂CLM_integral` build the
   complex-valued parameter integral by finite seminorm bounds and the
   integrablePower tail; `SCV.mixedRealFiberIntegralScalarCLM` packages it as
   a CLM; and
   `SCV.mixedRealFiberIntegralScalarCLM_eq_comp_mixedRealFiberIntegralCLM`
   plus
   `SCV.continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral`
   identify it with applying a base continuous functional after
   `SCV.mixedRealFiberIntegralCLM`.  This is the intended scalarized
   substitute for any unsupported Schwartz-valued Bochner integral.
   The parameter-kernel constructors and actual three-variable local descent
   tests are now checked up to their pointwise apply theorems:
   `SCV.realParamKernelLeft`, `SCV.realParamKernelRight`,
   `SCV.localDescentParamTestLeft`, and
   `SCV.localDescentParamTestRight`, all built by honest continuous linear
   equivalence precomposition.  Their remaining consumers are the two
   mixed-fiber change-of-variables identities and the local quotient theorem.
   The pure-SCV local-EOW support-preservation bridge needed before the
   distributional holomorphy integration-by-parts theorem is now checked in
   `SCV/DistributionalEOWSupport.lean`:

   ```lean
   theorem SCV.KernelSupportWithin_hasCompactSupport
   theorem SCV.directionalDerivSchwartzCLM_tsupport_subset
   theorem SCV.directionalDerivSchwartzCLM_supportsInOpen
   theorem SCV.dbarSchwartzCLM_tsupport_subset
   theorem SCV.SupportsInOpen.dbar
   ```

   This is not a wrapper layer.  It supplies the exact support hygiene required
   by the Streater-Wightman Theorem 2-16 regularization proof: radius-bounded
   kernels are compactly supported, and `dbarSchwartzCLM` preserves compact
   support inside the local open chart `U0`.
   The following `∂bar` integration-by-parts core is now checked and remains
   pure SCV:

   ```lean
   theorem SCV.integral_mul_directionalDerivSchwartzCLM_right_eq_neg_left
   theorem SCV.integral_mul_dbarSchwartzCLM_right_eq_neg_left
   theorem SCV.integral_mul_dbarSchwartzCLM_right_eq_zero_of_dbar_eq_zero
   theorem SCV.integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz
   theorem SCV.exists_smooth_cutoff_eq_one_near_tsupport_of_supportsInOpen
   theorem SCV.exists_local_schwartz_representative_eq_on_open
   theorem SCV.dbarSchwartzCLM_eq_zero_on_of_eqOn_holomorphic
   theorem SCV.exists_local_dbarClosed_schwartz_representative
   theorem SCV.integral_holomorphic_mul_dbarSchwartz_eq_zero
   theorem SCV.regularizedEnvelope_productKernel_dbar_eq_zero
   theorem SCV.translationCovariantKernel_distributionalHolomorphic
   theorem SCV.exists_normalized_schwartz_bump_kernelSupportWithin
   theorem SCV.exists_shrinking_normalized_schwartz_bump_sequence
   ```

   The first three are the global Schwartz-Schwartz identities.  The local
   Schwartz-representative algebra theorem is the endpoint: if a genuine
   Schwartz representative
   `G` agrees with the holomorphic-looking factor `F` on
   `tsupport (dbarSchwartzCLM j φ)` and `dbarSchwartzCLM j G = 0` on
   `tsupport φ`, then
   `∫ z, F z * (dbarSchwartzCLM j φ) z = 0`.  The cutoff theorem is also now
   checked: it constructs a smooth real compact cutoff equal to one on an open
   neighborhood of `tsupport φ` and topologically supported inside `U`.
   The zero-extension, smooth-to-Schwartz conversion, local Cauchy-Riemann
   pointwise theorem, representative theorem, and local holomorphic integral
   theorem are now checked as well:

   ```lean
   theorem SCV.exists_local_dbarClosed_schwartz_representative
       (U : Set (ComplexChartSpace m))
       (hU_open : IsOpen U)
       (F : ComplexChartSpace m -> ℂ)
       (hF_holo : DifferentiableOn ℂ F U)
       (φ : SchwartzMap (ComplexChartSpace m) ℂ)
       (hφ : SupportsInOpen (φ : ComplexChartSpace m -> ℂ) U)
       (j : Fin m) :
       ∃ G : SchwartzMap (ComplexChartSpace m) ℂ,
         (∀ z ∈ tsupport
             ((dbarSchwartzCLM j φ :
               SchwartzMap (ComplexChartSpace m) ℂ) :
               ComplexChartSpace m -> ℂ),
             F z = G z) ∧
         (∀ z ∈ tsupport (φ : ComplexChartSpace m -> ℂ),
             (dbarSchwartzCLM j G) z = 0)
   ```

   Its proof consumes the checked nested-thickening cutoff theorem, builds the
   zero-extended compactly supported smooth representative `χ * F`, converts it
   to a Schwartz function with `HasCompactSupport.toSchwartzMap`, and proves
   the coordinate Cauchy-Riemann identity on `tsupport φ` from
   `hF_holo.analyticOnNhd_of_finiteDimensional hU_open`.
   `SCV.integral_holomorphic_mul_dbarSchwartz_eq_zero` follows by one
   application of
   `SCV.integral_mul_dbarSchwartzCLM_right_eq_zero_of_left_local_schwartz`.
   The product-kernel consumer
   `SCV.regularizedEnvelope_productKernel_dbar_eq_zero` is now checked as
   well.  It uses `SupportsInOpen.dbar` to rewrite the product kernel on
   `schwartzTensorProduct₂ (dbarSchwartzCLM j φ) ψ` by the representing
   integral, then applies
   `SCV.integral_holomorphic_mul_dbarSchwartz_eq_zero` to `G ψ`.  The next
   continuity-passage theorem
   `SCV.translationCovariantKernel_distributionalHolomorphic` is also checked
   under the concrete approximate-identity hypotheses
   `∀ᶠ i, KernelSupportWithin (ψι i) r` and
   convergence of `realConvolutionTest θ (ψι i)` to `θ` in the Schwartz
   topology for every `θ`.  The next theorem-2 blocker in this SCV lane is
   therefore the genuine construction of that compact-supported approximate
   identity, not the local holomorphic cutoff bridge.  The exact next
   theorem surface
   `SCV.exists_normalized_schwartz_bump_kernelSupportWithin` is also now
   checked in pure SCV, as is
   `SCV.exists_shrinking_normalized_schwartz_bump_sequence`.  The remaining
   approximate-identity theorem surfaces
   `SCV.tendsto_realConvolutionTest_of_shrinking_normalized_support` and
   `SCV.exists_realConvolutionTest_approxIdentity` are also now checked.  The
   Lean proof follows the route pinned in
   `docs/scv_infrastructure_blueprint.md`: elementary kernel-mass/support and
   real-embedding lemmas, translated derivative integrability, zeroth-order
   and all-orders derivative-through-convolution identities, the global
   mean-value linear small-real-translation estimate for Schwartz derivatives,
   and the final seminorm-topology convergence theorem.  This remains pure SCV
   and does not introduce a bundled EOW wrapper or a Wightman-source import.
2. prove the strengthened Slot 1 surface above.  The coordinate prerequisites
   `BHW.configPermCLE`, `BHW.os45CommonChartCLE`,
   `BHW.wickRotate_ordered_mem_acrOne`,
   `BHW.adjacent_wick_traces_mem_acrOne`, and
   `BHW.os45CommonChart_real_mem_pulledRealBranchDomain_pair` are now checked.
   The local covariant product-kernel assembly
   `SCV.regularizedEnvelope_chartEnvelope_from_localCovariantProductKernel` is
   checked.  The proof-doc route now exposes the remaining SCV envelope
   assembly precisely: first derive the fixed-basis relatively compact side
   cone from `localEOWSimplexDirections ys` and convert the OS-II
   uniform-on-compact boundary hypotheses to raw `nhdsWithin` slice limits on
   that side cone and its negative image.  The side cone must come with both
   an open approach domain `Cplus ⊆ C` and a compact closed direction envelope
   fed to `TendstoUniformlyOn`; using the whole ambient cone `C` as the raw
   filter domain is not a valid substitute.  Next insert the affine real
   cutoff and package the two-sided slice CLMs through the checked
   `SCV.localEOWSliceCLMs_from_preparedDomains`, which internally uses
   `SCV.sliceCLM_family_from_distributionalBoundary_of_cutoffSupport` so the
   raw OS-II boundary values are applied only to compactly supported tests
   inside `E`; then prove
   `SCV.chartDistributionalEOW_local_envelope` with the chart-kernel family
   `Gchart ψ = Gorig (localEOWRealLinearKernelPushforwardCLM ys hli ψ)`;
   then transport and patch to formalize
   `SCV.local_distributional_edge_of_the_wedge_envelope`.  The local recovery
   theorem already performs the pointwise representation and delta-limit
   agreement internally, so the one-chart proof must feed it
   `exists_shrinking_normalized_schwartz_bump_sequence`,
   `tendsto_realConvolutionTest_of_shrinking_normalized_support`, and the
   side approximate-identity limits obtained from
   `regularizedEnvelope_kernelLimit_from_representation`, not add a separate
   free `hkernel_limit`.
   `OSReconstruction/SCV/LocalEOWSideCone.lean` now checks
   `SCV.tendsto_neg_nhdsWithin_zero_neg_image` and
   `SCV.localEOW_basisSideCone_rawBoundaryValue` in its strengthened explicit
   `ε` form, and
   `OSReconstruction/SCV/LocalDistributionalEOWSlice.lean` now checks
   `SCV.sliceCLM_family_from_distributionalBoundary` and the cutoff-support
   variant
   `SCV.sliceCLM_family_from_distributionalBoundary_of_cutoffSupport`.  The
   prepared-domain consumer is checked as
   `SCV.localEOWSliceCLMs_from_preparedDomains`.  The bounded side-margin
   packet is now checked as
   `SCV.exists_localEOW_truncatedSideCones_for_sliceMargin`, and the
   coordinate-radius shrink is checked as
  `SCV.exists_localEOWRealLinearPart_ball_subset`.  The prepared side-domain
   package is now checked as
   `SCV.localEOWPreparedSideDomains_from_fixedWindow`, and the fixed-window
   keystone assembly is now checked as
   `SCV.regularizedLocalEOW_chartEnvelope_from_fixedWindowScale`: from
   prepared fixed-window side domains, slice CLMs, cutoffs, closed support
   margins, and the one-chart scale inequalities, it constructs `Lorig`,
   `Lchart`, the mixed pairing CLM `K`, local covariance, the descent kernel,
   and the shrinking approximate-identity sequence, then call the checked
   scaled recovery theorem.  This one-chart assembly is now checked as
   `SCV.chartDistributionalEOW_local_envelope` in
   `SCV/LocalEOWDistributionalEnvelope.lean`: it constructs those prepared
   fixed-window inputs from the raw OS-II boundary-value hypotheses.  The
   distribution bookkeeping is part of the proof surface: the side-cone and
   slice-family steps use the original edge distribution `Torig`; the cutoff
   fixed-window family uses
   `TcutOrig = Torig.comp (SchwartzMap.smulLeftCLM ℂ χ)`; and the recovered
   chart distribution is
   `localEOWAffineDistributionPullbackCLM x0 ys hli TcutOrig`.  The local
   recovery theorem is instantiated with the chart-side functions
   `fun ζ => Fplus (localEOWChart x0 ys ζ)` and
   `fun ζ => Fminus (localEOWChart x0 ys ζ)`, with the checked
   `realMollifyLocal_localEOWChart_kernelPushforwardCLM_pullback` providing the
   side-mollifier change of variables.  No step treats the chart kernel as an
   original-coordinate kernel without this pushforward/Jacobian transport.
   The two small chart-linear real-window helpers documented in the SCV
   blueprint are now checked:
   `localEOWComplexAffineEquiv_symm_add_realEmbed` and
   `exists_localEOWRealLinearSymm_ball_subset`.  They make the affine
   cutoff-one and real-translation margin proof exact: the local real cutoff
   is the affine pushforward of a chart-coordinate cutoff, not an arbitrary
   original-coordinate cutoff.  The final one-chart implementation must keep
   the fixed-window polywedge radius and the product-kernel support radius
   separate: `rpoly` controls `localRudinEnvelope` side membership after
   truncating the side cones, while `rker` is the chart-kernel support radius
   used by the local covariant recovery theorem.  Reusing one variable `r` for
   both would hide a real smallness obligation.
   The final chart scale is chosen as in the SCV blueprint:
   `Rcore = rker = rη = σ`, `Rmix = 2σ`, `RmixCut = 4σ`,
   `Rdesc = 4σ`, `Rcov = 8σ`, `Rcut = 16σ`, with
   `128 * σ ≤ δ`, `4 * σ < δside`, `4 * σ < ρin`,
   `(Fintype.card (Fin m) : ℝ) * (4 * σ) < rpoly`, and
   `‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ * (4 * σ) ≤ rψOne`.
   Lean obtains the last inequality by calling
   `exists_oneChartRecoveryScale` with
   `M = 2 * ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖`,
   whose conclusion `(2 * M0) * (2 * σ) ≤ rψOne` rewrites to the required
   `M0 * (4 * σ) ≤ rψOne`.
   The cutoff radii are therefore fixed, not chosen later by convenience:
   `χr = 1` on `closedBall 0 (2σ)` and
   `tsupport χr ⊆ closedBall 0 (4σ)`, while
   `χψ = 1` on `closedBall 0 rψOne` and
   `tsupport χψ ⊆ closedBall 0 rψLarge` with `rψLarge` still inside the
   inverse-chart real-translation margin.  The original fixed-window family is
   instantiated at radius `rψLarge`; `rψOne` is only the smaller radius on
   which `χψ` is removed.  For local covariance, the checked adapter
   `regularizedLocalEOW_pairingCLM_localCovariant_from_fixedWindow` applies
   the shifted-overlap family covariance theorem.  Its two hypotheses
   `KernelSupportWithin ψ (2σ)` and
   `KernelSupportWithin (translateSchwartz a ψ) (2σ)` are pushed separately by
   `KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_of_le_four_mul`
   using `2σ ≤ 4σ` and
   `‖e‖ * (4σ) ≤ rψOne < rψLarge`.  This avoids any hidden claim
   that translation preserves a fixed support radius.  The continuity theorem
   `continuousOn_regularizedLocalEOW_chartKernelSliceIntegrand` is called
   with the compact real set
   `localEOWRealChart x0 ys '' closedBall 0 ρin`, not with the global open
   edge set.  The side identities and chart-family holomorphy are supplied by
   the fixed-window chart-kernel adapter
   `regularizedLocalEOW_chartKernelFamily_outputs_from_fixedWindow`, which
   first pushes support by
   `KernelSupportWithin.localEOWRealLinearKernelPushforwardCLM_of_le_four_mul`
   and then rewrites the side mollifiers with
   `realMollifyLocal_localEOWChart_kernelPushforwardCLM_pullback`.
   The side-function continuity inputs for the scaled recovery theorem are
   supplied by
   `chartSideFunction_continuousOn_strictBalls_from_fixedWindow`, using
   `4σ ≤ ρin` and `card * (4σ) < rpoly`.
   These inequalities close the real-window, truncated-side-cone,
   fixed-window coordinate-sum, pushed-kernel support, and local-recovery
   margin obligations on both the final core side ball and the larger
   side-neighborhood ball used by approximate identities.  In particular, the
   proof of the actual fixed-window `hplus/hminus` hypotheses for
   `Dplus/Dminus` has three separate components:
   fixed-window polywedge membership in `Ωplus/Ωminus`, truncated tube-domain
   membership in `TubeDomain CplusLoc/CminusLoc`, and affine real-window
   membership.  The translate-margin and slice cutoff-one hypotheses both use
   `localEOWAffineRealWindow_add_realEmbed`; the fact that the translated real
   point lies where the cutoff equals `1` implies it lies in `tsupport χ`, so
   `exists_localEOW_truncatedSideCones_for_sliceMargin` applies.  The
   approximate-identity side limits are the checked strict-side packages
   `tendsto_realMollifyLocal_strictPositiveImagBall` and
   `tendsto_realMollifyLocal_strictNegativeImagBall`; internally they apply
   `regularizedEnvelope_kernelLimit_from_representation` on the positive and
   negative chart-side neighborhoods, with
   `StrictPositiveImagBall_add_realEmbed_mem_ball_of_norm_le` and
   `StrictNegativeImagBall_add_realEmbed_mem_ball_of_norm_le` giving the exact
   real-translation margins for kernels supported in `closedBall 0 σ`.  The
   representation identity then unfolds `realMollifyLocal`; no free
   `hkernel_limit` or slow-growth input is permitted in the one-chart theorem.
   The scaled local-recovery call itself is now checked as
   `regularizedEnvelope_chartEnvelope_from_oneChartScale`: it fixes
   `Ucore = ball 0 σ`, `Udesc = ball 0 (4σ)`, `Ucov = ball 0 (8σ)`,
   `U0 = ball 0 (δ / 2)`, `DplusSmall = StrictPositiveImagBall σ`,
   `DminusSmall = StrictNegativeImagBall σ`, and derives
   `happrox_plus/happrox_minus` from the strict-side convergence theorems.
   The next SCV target is the genuine affine transport
   `SCV.chartDistributionalEOW_transport_originalCoords`, followed by the
   fixed-basis overlap package
   `SCV.localEOWComplexAffineEquiv_sameBasis_transition`,
   `SCV.localEOWFixedBasisCoordinateOverlap`,
   `SCV.localEOWFixedBasis_overlap_positiveSeed`, and
   `SCV.distributionalEOW_extensions_compatible`, then by the patching theorem
   `SCV.local_distributional_edge_of_the_wedge_envelope`.
   Only after that prove the OS45 instantiation
   `BHW.os45_adjacent_commonBoundaryEnvelope` and package its output as
   `AdjacentOSEOWDifferenceEnvelope` while exporting the same patch `V` for
   Jost membership and both real extended-tube memberships;
3. use the checked
   `BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch`,
   the genuine Hall-Wightman scalar-product-variety real-environment theorem
   packaged for the Gram image of the selected Jost patch;
4. implement
   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII` from exactly
   those two inputs and the checked compact-test theorem
   `BHW.bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`;
5. pass that data through the already checked
   `bvt_F_distributionalJostAnchor_of_selectedJostData` bridge;
6. only then close the source-backed BHW theorem
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
   and its sector-equality specialization to `bvt_F`.

No `d = 1` implementation, imported boundary-locality theorem, theorem-4 work,
or generic permutation-flow endgame belongs to this stage.  The older
`SelectedAdjacentPermutationEdgeData` packet below is retained as audited
background, but it is not allowed to supply the distributional Jost anchor
because it forgets the scalar-product real environment and the compact
boundary-distribution data.

### Slot 2. `bvt_F_adjacent_edgeWitness_from_OS_ACR_of_two_le`

Once Slot 1 exists, the compact-test edge theorem is already checked:
`bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`.

The following selected-edge theorem is therefore only a historical/background
packaging theorem for the older selected-permutation edge packet, not the
active implementation gate for theorem 2:

```lean
theorem bvt_F_adjacent_edgeWitness_from_OS_ACR_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∃ V : Set (NPointDomain d n),
        IsOpen V ∧ V.Nonempty ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
        (∀ x ∈ V,
          BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n -> ℂ) ->
          tsupport (φ : NPointDomain d n -> ℂ) ⊆ V ->
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed
                  (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
            =
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
```

Proof:

- obtain `V`, `rho`, and an envelope from Slot 1;
- use `bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`;
- discharge the ET-membership hypotheses from `os45_adjacent_localEOWGeometry`.

### Slot 3. `adjacent_extendedTube_overlap_connected`

The selected edge-data structure also needs overlap connectedness:

```lean
theorem adjacent_extendedTube_overlap_connected
    [NeZero d]
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    IsConnected
      {z : Fin n -> Fin (d + 1) -> ℂ |
        z ∈ BHW.ExtendedTube d n ∧
          BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
            BHW.ExtendedTube d n}
```

This is not an OS-side locality theorem.  It is the pure BHW adjacent-overlap
geometry needed by the selected-adjacent edge packet.  The current checked Lean
handoff

```lean
bvt_selectedAdjacentOverlap_connected_of_permSeedGeometry
```

proves the displayed statement from:

```lean
BHW.isConnected_adjSwapExtendedOverlap_of_forwardOverlapConnected
BHW.isConnected_permSeedSet_iff_permForwardOverlapSet
BHW.blocker_isConnected_permSeedSet_nontrivial
```

That is honest but broader than theorem 2 needs.  The preferred theorem-2 proof
doc should narrow the mathematical debt to the adjacent-swap geometry:

```lean
theorem BHW.adjSwapForwardOverlapIndexSet_real_double_coset_generation_hd2
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (Λ0 : ComplexLorentzGroup d)
    (hΛ0 : Λ0 ∈
      BHW.adjSwapForwardOverlapIndexSet (d := d) n i hi) :
    ∀ Λ ∈ BHW.adjSwapForwardOverlapIndexSet (d := d) n i hi,
      ∃ R1 R2 : RestrictedLorentzGroup d,
        Λ = ComplexLorentzGroup.ofReal R1 * Λ0 *
          ComplexLorentzGroup.ofReal R2

theorem BHW.adjacent_extendedTube_overlap_connected_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    IsConnected
      {z : Fin n -> Fin (d + 1) -> ℂ |
        z ∈ BHW.ExtendedTube d n ∧
          BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
            BHW.ExtendedTube d n} := by
  classical
  have hne :
      (BHW.adjSwapForwardOverlapSet (d := d) n i hi).Nonempty :=
    BHW.adjSwapForwardOverlap_nonempty (d := d) n i hi
  obtain ⟨Λ0, hΛ0⟩ :=
    BHW.nonempty_adjSwapForwardOverlapIndexSet_of_forwardOverlapNonempty'
      (d := d) n i hi hne
  have hFwd :
      IsConnected (BHW.adjSwapForwardOverlapSet (d := d) n i hi) :=
    BHW.isConnected_adjSwapForwardOverlapSet_of_real_double_coset_generation
      (d := d) n i hi Λ0 hΛ0
      (BHW.adjSwapForwardOverlapIndexSet_real_double_coset_generation_hd2
        (d := d) hd n i hi Λ0 hΛ0)
  simpa [BHW.adjSwapExtendedOverlapSet, BHW.permAct] using
    BHW.isConnected_adjSwapExtendedOverlap_of_forwardOverlapConnected
      (d := d) n i hi hFwd
```

The proof of the double-coset generation theorem is the genuine geometry:
normalize any adjacent forward-overlap witness by real restricted Lorentz
transformations so that the ordered and swapped forward-cone pairs sit in the
same two-plane normal form.  It must use only the connected real Lorentz group,
the forward-cone geometry, and the adjacent-swap witness; it must not use
locality or any Wightman permutation symmetry.

### Slot 4. `bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le`

This is the final `2 <= d` supplier theorem:

```lean
theorem bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SelectedAdjacentPermutationEdgeData OS lgc n
```

Proof:

- `overlap_connected` comes from Slot 3;
- `edge_witness` comes from Slot 2.

That theorem is the exact handoff point from the new OS45 local work to the
already checked selected-witness / PET side.

Checked route update: the selected-witness file now has the intermediate
handoff

```lean
theorem bvt_F_selectedAdjacentPermutationEdgeData_of_selectedJostData_and_permSeedGeometry
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n) :
    SelectedAdjacentPermutationEdgeData OS lgc n
```

This theorem discharges the `overlap_connected` field using existing BHW
geometry:

- `BHW.isConnected_adjSwapExtendedOverlap_of_forwardOverlapConnected`;
- `BHW.isConnected_permSeedSet_iff_permForwardOverlapSet`;
- the existing pure-geometry blocker
  `BHW.blocker_isConnected_permSeedSet_nontrivial`.

Therefore Slot 4 is now reduced to constructing
`SelectedAdjacentDistributionalJostAnchorData OS lgc n`.  The adjacent
ET-overlap connectedness should no longer be treated as an independent OS-side
hypothesis; it is a BHW geometry dependency already exposed in the Lean
dependency graph.

## 5. Exact downstream chain after Slot 4 for `2 <= d`

After Slot 4, no new OS45 local geometry is allowed.  The remaining work is the
literal BHW/PET/Jost endgame.  The exact order below is now part of the
implementation contract.

### Slot 5. `bvt_F_adjacent_sector_compatibility_of_two_le`

This is a small wrapper theorem turning Slot 4 into the exact `hAdj` hypothesis
consumed by `PermutedTubeMonodromy.lean`.

```lean
theorem bvt_F_adjacent_sector_compatibility_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n) :
    ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
      (z : Fin n -> Fin (d + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π ->
      z ∈ BHW.permutedExtendedTubeSector d n
        (π * Equiv.swap i ⟨i.val + 1, hi⟩) ->
      BHW.extendF (bvt_F OS lgc n)
        (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k))
```

Proof transcript:

1. apply `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`,
2. unfold `bvt_selectedPETBranch`,
3. rewrite the result into the displayed `extendF` branch equality.

Lean pseudocode:

```lean
  intro π i hi z hzπ hzπswap
  simpa [bvt_selectedPETBranch] using
    bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
      (d := d) OS lgc n hEdge π i hi z hzπ hzπswap
```

This wrapper is theorem-2-facing only; it must not introduce any new geometry
or any all-permutation edge-data structure.

### Archived Slot 6 alternative. `petOrbitChamberConnected_of_two_le`

This is conditional monodromy infrastructure, not the active theorem-2 Slot 6.
The strict OS I §4.5 route now consumes the direct source-backed
Hall-Wightman/BHW single-valuedness theorem on `S''_n`.  The checked
reachable-label form displayed below remains useful background only if a future
source audit proves it as a faithful decomposition of that source theorem.

The proposed `petOrbitChamberConnected_of_two_le` route was attractive because
it would have fed the checked monodromy theorem
`BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`.
It is not the current route.  What must not be revived is the concrete
finite-chain packet that strengthened the edge relation to a common fixed-`w`
**permuted forward-tube** slice.  That stronger edge cannot exist for distinct
adjacent labels.

```lean
theorem petOrbitChamberConnected_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ BHW.ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ ->
        Relation.ReflTransGen
          (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ
```

Reason for rejection:

1. `BHW.PermutedForwardTube d n π` is defined by
   `(fun k => z (π k)) ∈ BHW.ForwardTube d n`.
2. The repo already proves the disjointness/uniqueness facts
   `BHW.forwardTube_inter_permutedForwardTube_eq_empty_of_ne_one` and
   `BHW.permutedForwardTube_sector_eq_of_mem`.
3. Therefore, if one transformed point lies in both
   `BHW.PermutedForwardTube d n π` and
   `BHW.PermutedForwardTube d n ρ`, then `π = ρ`.  For an adjacent step
   `ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩`, this is impossible.
4. Consequently the fixed-`w` chain packet requiring common
   `PermutedForwardTube` slice witnesses is not a difficult missing
   chamber-stratification theorem; it is the wrong theorem surface.

Correct active replacement:

Slot 6 proves or explicitly source-imports
`hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor` from
the Hall-Wightman scalar-product geometry and the OS-II selected
distributional/Jost anchor.  The following reachable-label `hOrbit` theorem may
remain as a conditional monodromy consumer, but it is not the OS-paper
implementation gate.  The source theorem must not use locality or any theorem
whose proof uses locality.  It also must not rely on total `hF_perm` values
outside the ordered forward tube as if they were boundary data.

The following hF_perm-only statement is kept as an archived unsafe
intermediate because it is the current Lean theorem name and explains the
downstream API shape.  It is **not** the statement to close as a source
theorem:

```lean
theorem BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n -> Fin (d + 1) -> ℂ),
        z ∈ BHW.ForwardTube d n ->
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n -> Fin (d + 1) -> ℂ),
        F (fun k => z (σ k)) = F z) :
    ∃ Fpet : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ,
      DifferentiableOn ℂ Fpet (BHW.PermutedExtendedTube d n) ∧
      ∀ (π : Equiv.Perm (Fin n))
        (z : Fin n -> Fin (d + 1) -> ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π ->
        Fpet z = BHW.extendF F (fun k => z (π k))
```

The theorem-2-facing source extension theorem is the planned PET-algebra
assembly from the corrected distributionally anchored branch law.  Its Lean
surface should carry the explicit source anchor and then remain a mechanical
consumer:

```lean
theorem BHW.permutedExtendedTube_extension_of_forwardTube_symmetry
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n -> Fin (d + 1) -> ℂ),
        z ∈ BHW.ForwardTube d n ->
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n -> Fin (d + 1) -> ℂ),
        F (fun k => z (σ k)) = F z)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F) :
    ∃ Fpet : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ,
      DifferentiableOn ℂ Fpet (BHW.PermutedExtendedTube d n) ∧
      (∀ z ∈ BHW.ForwardTube d n, Fpet z = F z) ∧
      (∀ (π : Equiv.Perm (Fin n))
        (z : Fin n -> Fin (d + 1) -> ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π ->
        Fpet z = BHW.extendF F (fun k => z (π k))) ∧
      (∀ (Λ : ComplexLorentzGroup d)
        (z : Fin n -> Fin (d + 1) -> ℂ),
        z ∈ BHW.PermutedExtendedTube d n ->
        BHW.complexLorentzAction Λ z ∈ BHW.PermutedExtendedTube d n ->
        Fpet (BHW.complexLorentzAction Λ z) = Fpet z) ∧
      (∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n -> Fin (d + 1) -> ℂ),
        z ∈ BHW.PermutedExtendedTube d n ->
        (fun k => z (σ k)) ∈ BHW.PermutedExtendedTube d n ->
        Fpet (fun k => z (σ k)) = Fpet z)
```

The branch law says exactly that the single function on `S''_n` restricts on
the `π`-sector to the ordinary BHW extended-tube branch
`BHW.extendF F (fun k => z (π k))`.  The larger theorem proves the
forward-tube agreement and PET Lorentz/permutation invariance from that branch
law using sector transport and `BHW.extendF_complex_lorentz_invariant`.

The theorem-2-facing equality theorem is then the immediate branch-law
corollary:

```lean
theorem BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n -> Fin (d + 1) -> ℂ),
        z ∈ BHW.ForwardTube d n ->
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n -> Fin (d + 1) -> ℂ),
        F (fun k => z (σ k)) = F z)
    (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (d + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π ->
      z ∈ BHW.permutedExtendedTubeSector d n ρ ->
      BHW.extendF F (fun k => z (π k)) =
        BHW.extendF F (fun k => z (ρ k))
```

Lean-shaped derivation from the source theorem:

```lean
  intro π ρ z hzπ hzρ
  obtain ⟨Fpet, hFpet_holo, hFpet_FT, hFpet_branch,
      hFpet_lorentz, hFpet_perm⟩ :=
    BHW.permutedExtendedTube_extension_of_forwardTube_symmetry
      (d := d) hd n F hF_holo hF_lorentz hF_perm hAnchor
  exact (hFpet_branch π z hzπ).symm.trans (hFpet_branch ρ z hzρ)
```

Together the branch-law theorem, the extension assembly theorem, and the
branch-equality corollary are the direct local Lean form of the OS I §4.5 use
of Hall-Wightman/BHW: a real-Lorentz-invariant symmetric holomorphic datum on
the permuted forward-tube family `S'_n` has a single-valued symmetric
`L_+(ℂ)`-invariant continuation on the complex-Lorentz saturation `S''_n`.

Implementation discipline: the branch-law theorem is the only theorem-level
analytic frontier in `SourceExtension.lean`; the source extension theorem and
the branch-equality theorem are mechanical consumers of it.  None of these
theorems may be introduced as an `axiom` without the user's explicit approval.
All statements are intentionally pure SCV/BHW and contain no OS or QFT-specific
objects.

Internal contract for the branch-law proof after the source-surface refactor:

1. keep the branch family explicit:

   ```lean
   let G : (π : Equiv.Perm (Fin n)) ->
       (Fin n -> Fin (d + 1) -> ℂ) -> ℂ :=
     fun π z => BHW.extendF F (fun k => z (π k))
   ```

2. prove `∀ π, DifferentiableOn ℂ (G π)
   (BHW.permutedExtendedTubeSector d n π)` by the already checked theorem
   `BHW.permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz`;
3. build the `S'_n` source datum from the forward-tube restrictions
   `z ∈ BHW.PermutedForwardTube d n π ↦ F (fun k => z (π k))`, but identify
   it as symmetric only through the Euclidean/Jost anchor: Schwinger symmetry
   on the real uniqueness set and branch agreement with the Schwinger
   function there.  The raw total `hF_perm` hypothesis is not enough for this
   source step;
4. apply the Hall-Wightman/BHW scalar-product source theorem to that
   Euclidean-anchored symmetric `S'_n` datum, producing one holomorphic
   `Fpet` on `BHW.PermutedExtendedTube d n`;
5. identify the restriction of this source `Fpet` on each explicit PET sector
   with the already-defined branch `G π`;
6. return exactly the existential statement of
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`.

Any family-indexed helper introduced to organize these steps must stay local
to the branch-law proof or be a plainly source-facing lemma consumed
immediately by it.  It must not become a new public theorem-2 wrapper, must not
assume sector compatibility on `S''_n`, and must not use
`BHW.gluedPETValue_holomorphicOn`, since that theorem assumes the compatibility
that Hall-Wightman is supposed to provide.

Existing repo API audit for this proof:

1. `BHW.extendF`, `BHW.extendF_preimage_eq`,
   `BHW.extendF_eq_on_forwardTube`, and
   `BHW.extendF_complex_lorentz_invariant` already formalize the ordinary
   one-forward-tube Hall-Wightman continuation to `BHW.ExtendedTube d n`;
2. `BHW.permutedExtendedTube_isPreconnected` and
   `BHW.isConnected_permutedExtendedTube` supply the topology of the explicit
   PET sector cover, but topology alone does not compare the analytic branch
   values on sector overlaps;
3. `BHW.gluedPETValue` and `BHW.gluedPETValue_holomorphicOn` are therefore
   downstream packaging only: they can name the `Fpet` after the source theorem
   supplies compatibility, but they cannot be used to prove that compatibility.

Lean lemma ladder for the branch-law proof:

The implementation should keep the following as private proof-local facts in
`SourceExtension.lean` unless one of them is already available under a checked
name.  They are not new theorem-2 wrappers; they only spell out the source
datum that Hall-Wightman consumes.

1. **Permuted forward-tube branches.**

   ```lean
   let Gpft : (π : Equiv.Perm (Fin n)) ->
       (Fin n -> Fin (d + 1) -> ℂ) -> ℂ :=
     fun π z => F (fun k => z (π k))
   ```

   The elementary local theorem is:

   ```lean
   private theorem source_permutedForwardBranch_holomorphicOn
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (π : Equiv.Perm (Fin n)) :
       DifferentiableOn ℂ
         (fun z : Fin n -> Fin (d + 1) -> ℂ => F (fun k => z (π k)))
         (BHW.PermutedForwardTube d n π)
   ```

   This is just `hF_holo.comp` with the continuous coordinate-permutation map.

2. **Restricted Lorentz invariance on each permuted forward tube.**

   ```lean
   private theorem source_permutedForwardBranch_restrictedLorentzInvariant
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (π : Equiv.Perm (Fin n)) :
       ∀ (Λ : RestrictedLorentzGroup d)
         (z : Fin n -> Fin (d + 1) -> ℂ),
         z ∈ BHW.PermutedForwardTube d n π ->
         (fun z' : Fin n -> Fin (d + 1) -> ℂ =>
             F (fun k => z' (π k)))
           (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z) =
         F (fun k => z (π k))
   ```

   The proof uses the already checked commutation of Lorentz action with
   coordinate permutations and the fact that `ComplexLorentzGroup.ofReal Λ`
   preserves the forward tube.

3. **Symmetry of the `S'_n` datum before BHW enlargement.**

   ```lean
   private theorem source_permutedForwardBranch_symmetric
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_perm :
         ∀ (σ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (σ k)) = F z) :
       ∀ (π ρ : Equiv.Perm (Fin n))
         (z : Fin n -> Fin (d + 1) -> ℂ),
         F (fun k => z (π k)) = F (fun k => z (ρ k))
   ```

   This is the exact place where `hF_perm` enters the `S'_n` source datum.  It
   must not be confused with the false PET shortcut
   `BHW.extendF F (fun k => z (π k)) =
    BHW.extendF F (fun k => z (ρ k))`, which is the Hall-Wightman output.

4. **Source compatibility theorem after the datum is packaged.**

   With the three local facts above in scope, the only remaining
   non-elementary theorem is cross-sector compatibility supplied by
   Hall-Wightman single-valuedness plus the OS-II distributional anchor.  The
   Lean surface has now been refactored so that the distributional anchor is
   an explicit input:

   ```lean
   private theorem hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (hF_perm :
         ∀ (σ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (σ k)) = F z)
       (hAnchor : SourceDistributionalAdjacentTubeAnchor (d := d) n F) :
       ∀ (π ρ : Equiv.Perm (Fin n))
         (z : Fin n -> Fin (d + 1) -> ℂ),
         z ∈ BHW.permutedExtendedTubeSector d n π ->
         z ∈ BHW.permutedExtendedTubeSector d n ρ ->
         BHW.extendF F (fun k => z (π k)) =
           BHW.extendF F (fun k => z (ρ k))
   ```

   The wrapper
   `hallWightman_source_permutedBranch_compatibility` has the same anchor in
   its hypotheses and immediately calls this theorem.  The
   fixed-sector graph lemmas in `PermutedTubeMonodromy.lean` remain useful
   checked algebra for adjacent-to-all propagation, but they are not a public
   Hall-Wightman hypothesis for theorem 2.  OS I §4.5 invokes
   Hall-Wightman as the single-valuedness theorem on the whole `S''_n`, so any
   sector-chain or cover-connectivity argument belongs inside the source
   theorem proof, not in the theorem-2 consumer surface.  This is
   the exact mathematical point where Hall-Wightman enters: the
   symmetric `S'_n` datum has a single-valued continuation on `S''_n`, so two
   explicit PET sector branches that meet at the same point have the same
   value.  It is not a wrapper; it is the genuine source content.  The proof
   docs should not ask Lean to prove this from `BHW.gluedPETValue`, because
   gluing assumes this compatibility.  It must not be introduced as an axiom or
   imported source theorem without the separate explicit approval, source
   audit, and circularity audit required by `AGENT.md`.

   Source-scope sanity check:

   - The approved Gemini Deep Research route
     (`deep-research-pro-preview-12-2025`, Interactions API, 2026-04-24)
     found the hF_perm-only generic theorem surface mathematically unsafe.
     Because the ordered forward tube is disjoint from its nontrivial
     permuted copies, a total Lean hypothesis
     `F (fun k => z (σ k)) = F z` can be satisfied by off-domain "junk
     values" and does not constrain the analytic germ on the ordered forward
     tube.  This is the same trap already documented in
     `BHWReducedExtension.lean` for the removed raw reduced BHW axiom.
   - Therefore the currently displayed generic source theorem cannot be
     justified from `hF_holo`, `hF_lorentz`, and total `hF_perm` alone.  The
     correct OS I §4.5 source surface must include the distributional
     Euclidean/Jost uniqueness anchor: compact-test Schwinger symmetry on
     permutation-indexed real patches, agreement of the BHW branch boundary
     distributions with the Schwinger distribution there, and the
     distributional EOW/identity theorem on the scalar-product variety.
   - Growth/temperedness is not an extra hypothesis of the isolated
     Hall-Wightman uniqueness step once the holomorphic `F` and distributional
     Euclidean matching are available.  It remains essential upstream in the
     OS-II-corrected construction of `bvt_F` and its tempered boundary values
     from Schwinger data.
   - The theorem statement remains exactly for `hd : 2 <= d`.  If a later
     source audit found that an imported Hall-Wightman formulation only covers
     a stricter dimension range, the theorem surface would need a documented
     split before implementation.  No such split is currently authorized.
   - A further Deep Research route-risk check
     (`v1_ChdUSW5yYWFuUkhNNlVfdU1QOE9YaGtRWRIXVElucmFhblJITTZVX3VNUDhPWGhrUVk`)
     rejected making `BHW.petSectorFiber_adjacent_connected_of_two_le` a
     theorem-2 prerequisite.  The fixed-point sector-fiber chain is not a
     theorem in OS I, OS II, or Hall-Wightman, and it is at best a separate
     hard PET-geometry project.  The theorem-2 source surface must state
     Hall-Wightman single-valuedness on `S''_n` directly from the symmetric
     distributionally anchored `S'_n` datum.

   The compatibility theorem now has the right implementation-ready surface:
   the following distributional Euclidean/Jost-anchored Hall-Wightman/EOW
   source theorem.  This theorem is the precise source consequence needed
   here; it is not a wrapper and it is not allowed to be introduced as an
   axiom without the `AGENT.md` approval gate.

   First define the complex Minkowski Gram matrix of the ordered vector tuple:

   ```lean
   private def sourceMinkowskiGram (d n : ℕ)
       (x : Fin n -> Fin (d + 1) -> ℂ) :
       Fin n -> Fin n -> ℂ :=
     fun i j =>
       ∑ μ : Fin (d + 1),
         (MinkowskiSpace.metricSignature d μ : ℂ) * x i μ * x j μ
   ```

   Follow-up Deep Research check
   `v1_ChdOWVRyYWQzZ0xhRFFfdU1Qb19ud3FRTRIXTllUcmFkM2dMYURRX3VNUG9fbndxUU0`
   rejected the tempting **single pointwise** `E, S` anchor as overstrong for
   this repo.  The reasons are concrete:

   - the local `JostSet` is not globally known to lie in `ExtendedTube`; the
     repo even records the global `JostSet -> ExtendedTube` bridge as false;
   - OS data is distributional (`OS.S n : ZeroDiagonalSchwartz d n -> ℂ`),
     and the available Lean facts are compact-test equalities such as
     `bvt_euclidean_restriction` and
     `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`;
   - the already-built OS45 infrastructure constructs real-open **adjacent**
     edge slices, not one real open set that lies in every permuted sector.

   Therefore the source theorem must be stated with permutation-indexed
   real-open patches and compact-test distributional anchors.  A pointwise
   scalar-product representative is a Hall-Wightman consequence after this
   anchor has been supplied; it is not the input shape for the OS-II Lean
   route.

   The active source package is the following theorem-surface shape, now
   implemented in
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtension.lean`.
   The pure BHW file deliberately spells the real configuration space as
   `Fin n -> Fin (d + 1) -> ℝ` rather than importing the OS-side abbreviation
   `NPointDomain d n`; `NPointDomain` is definitionally this tuple type in the
   reconstruction layer.

   ```lean
   private def sourceRealMinkowskiGram (d n : ℕ)
       (x : Fin n -> Fin (d + 1) -> ℝ) :
       Fin n -> Fin n -> ℝ :=
     fun i j =>
       ∑ μ : Fin (d + 1),
         MinkowskiSpace.metricSignature d μ * x i μ * x j μ

   private def sourcePermuteGram (n : ℕ)
       (σ : Equiv.Perm (Fin n))
       (G : Fin n -> Fin n -> ℝ) :
       Fin n -> Fin n -> ℝ :=
     fun i j => G (σ i) (σ j)

   structure SourceDistributionalAdjacentTubeAnchor
       [NeZero d]
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) where
     realPatch :
       Equiv.Perm (Fin n) ->
       (i : Fin n) ->
       (hi : i.val + 1 < n) ->
       Set (Fin n -> Fin (d + 1) -> ℝ)
     realPatch_open :
       ∀ π i hi, IsOpen (realPatch π i hi)
     realPatch_nonempty :
       ∀ π i hi, (realPatch π i hi).Nonempty
     realPatch_jost :
       ∀ π i hi, realPatch π i hi ⊆ BHW.JostSet d n
     realPatch_left_sector :
       ∀ π i hi x, x ∈ realPatch π i hi ->
         BHW.realEmbed (d := d) x ∈
           BHW.permutedExtendedTubeSector d n π
     realPatch_right_sector :
       ∀ π i hi x, x ∈ realPatch π i hi ->
         BHW.realEmbed (d := d) x ∈
           BHW.permutedExtendedTubeSector d n
             (π * Equiv.swap i ⟨i.val + 1, hi⟩)
     gramEnvironment :
       Equiv.Perm (Fin n) ->
       (i : Fin n) ->
       (hi : i.val + 1 < n) ->
       Set (Fin n -> Fin n -> ℝ)
     gramEnvironment_unique :
       ∀ π i hi,
         BHW.sourceDistributionalUniquenessSetOnVariety d n
           (gramEnvironment π i hi)
     gram_left_mem :
       ∀ π i hi x, x ∈ realPatch π i hi ->
         sourceRealMinkowskiGram d n (fun k => x (π k)) ∈
           gramEnvironment π i hi
     gram_environment_realized :
       ∀ π i hi G, G ∈ gramEnvironment π i hi ->
         ∃ x ∈ realPatch π i hi,
           sourceRealMinkowskiGram d n (fun k => x (π k)) = G
     gram_right_eq_perm_left :
       ∀ π i hi x, x ∈ realPatch π i hi ->
         sourceRealMinkowskiGram d n
             (fun k => x ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
           sourcePermuteGram n (Equiv.swap i ⟨i.val + 1, hi⟩)
             (sourceRealMinkowskiGram d n (fun k => x (π k)))
     compact_branch_eq :
       ∀ π i hi (φ : SchwartzMap (Fin n -> Fin (d + 1) -> ℝ) ℂ),
         HasCompactSupport
           (φ : (Fin n -> Fin (d + 1) -> ℝ) -> ℂ) ->
         tsupport (φ : (Fin n -> Fin (d + 1) -> ℝ) -> ℂ) ⊆
           realPatch π i hi ->
         ∫ x : Fin n -> Fin (d + 1) -> ℝ,
             BHW.extendF F (fun k => BHW.realEmbed (d := d) x (π k)) *
               φ x
           =
         ∫ x : Fin n -> Fin (d + 1) -> ℝ,
             BHW.extendF F
               (fun k =>
                 BHW.realEmbed (d := d) x
                   ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) *
               φ x
   ```

   The corresponding Hall-Wightman/EOW source theorem is:

   ```lean
   private theorem hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (hF_perm :
         ∀ (σ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (σ k)) = F z)
       (hAnchor :
         SourceDistributionalAdjacentTubeAnchor (d := d) n F) :
       ∀ (π ρ : Equiv.Perm (Fin n))
         (z : Fin n -> Fin (d + 1) -> ℂ),
         z ∈ BHW.permutedExtendedTubeSector d n π ->
         z ∈ BHW.permutedExtendedTubeSector d n ρ ->
         BHW.extendF F (fun k => z (π k)) =
           BHW.extendF F (fun k => z (ρ k))
   ```

   Its proof is the real mathematical source step:

   1. for each adjacent step, use Hall-Wightman to represent the two adjacent
      branches by scalar-product holomorphic representatives;
   2. use `hAnchor.compact_branch_eq` on the indexed real patch to get equality
      of the adjacent boundary distributions on a real environment in
      scalar-product space;
   3. apply distributional edge-of-the-wedge / totally-real uniqueness on that
      real environment to identify the adjacent scalar-product
      representatives;
   4. conclude the all-sector branch law on `S''_n` as the Hall-Wightman
      single-valued continuation theorem.  If the internal proof is organized
      through adjacent real environments, the required cover-continuation
      argument is part of this source theorem.  It must not appear as a
      separate theorem-2 hypothesis such as
      `BHW.petSectorFiber_adjacent_connected_of_two_le`.

   This is the precise place where a future theorem may produce a pointwise
   scalar representative
   `Φ (sourceMinkowskiGram d n z)`.  That representative is an output of the
   source theorem, not an OS input.

   Do not replace this source theorem by an ordinary
   `BHW.extendF F (x ∘ σ) = BHW.extendF F x` theorem as the primary source
   input.  Such a theorem may be a derived corollary after the branch-level
   scalar-product representative is known, but using it as the source boundary
   hides the `S'_n` content and risks over-reading the total `hF_perm`
   hypothesis on the ordered forward tube.

   Full Lean-ready Hall-Wightman scalar-product packet:

   The source theorem should be proved in scalar-product coordinates before it
   is translated back to PET sector branches.  The following checked
   definitions now exist in `SourceExtension.lean` and must be used rather
   than ad hoc matrix manipulation:

   ```lean
   def BHW.sourcePermuteComplexGram
       (n : ℕ)
       (σ : Equiv.Perm (Fin n))
       (Z : Fin n -> Fin n -> ℂ) :
       Fin n -> Fin n -> ℂ :=
     fun i j => Z (σ i) (σ j)

   theorem BHW.sourceMinkowskiGram_perm
       (d n : ℕ)
       (σ : Equiv.Perm (Fin n))
       (z : Fin n -> Fin (d + 1) -> ℂ) :
       BHW.sourceMinkowskiGram d n (fun k => z (σ k)) =
         BHW.sourcePermuteComplexGram n σ
           (BHW.sourceMinkowskiGram d n z)

   def BHW.sourceExtendedTubeGramDomain (d n : ℕ) :
       Set (Fin n -> Fin n -> ℂ) :=
     BHW.sourceMinkowskiGram d n '' BHW.ExtendedTube d n

   def BHW.sourceDoublePermutationGramDomain
       (d n : ℕ)
       (σ : Equiv.Perm (Fin n)) :
       Set (Fin n -> Fin n -> ℂ) :=
     {Z | Z ∈ BHW.sourceExtendedTubeGramDomain d n ∧
       BHW.sourcePermuteComplexGram n σ Z ∈
         BHW.sourceExtendedTubeGramDomain d n}

   theorem BHW.sourceRealMinkowskiGram_perm
       (d n : ℕ)
       (σ : Equiv.Perm (Fin n))
       (x : Fin n -> Fin (d + 1) -> ℝ) :
       BHW.sourceRealMinkowskiGram d n (fun k => x (σ k)) =
         BHW.sourcePermuteGram n σ
           (BHW.sourceRealMinkowskiGram d n x)

   theorem BHW.sourceRealGramComplexify_perm
       (n : ℕ)
       (σ : Equiv.Perm (Fin n))
       (G : Fin n -> Fin n -> ℝ) :
       BHW.sourceRealGramComplexify n
           (BHW.sourcePermuteGram n σ G) =
         BHW.sourcePermuteComplexGram n σ
           (BHW.sourceRealGramComplexify n G)
   ```

   The scalar-product representative supplied by Hall-Wightman Theorem I
   should be packaged as data, not as a pointwise shortcut:

   ```lean
   structure BHW.SourceScalarRepresentativeData
       [NeZero d]
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ) where
     U : Set (Fin n -> Fin n -> ℂ)
     U_eq :
       U = BHW.sourceExtendedTubeGramDomain d n
     U_relOpen :
       BHW.IsRelOpenInSourceComplexGramVariety d n U
     U_connected :
       IsConnected U
     Phi : (Fin n -> Fin n -> ℂ) -> ℂ
     Phi_holomorphic :
       BHW.SourceVarietyHolomorphicOn d n Phi U
     branch_eq :
       ∀ w : Fin n -> Fin (d + 1) -> ℂ,
         w ∈ BHW.ExtendedTube d n ->
         Phi (BHW.sourceMinkowskiGram d n w) =
           BHW.extendF F w
   ```

   The first non-elementary theorem is exactly Hall-Wightman's invariant
   analytic-function theorem for the ordinary extended tube:

   ```lean
   theorem BHW.hallWightman_exists_sourceScalarRepresentative_of_forwardTube_lorentz
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
       ∃ hRep : BHW.SourceScalarRepresentativeData (d := d) n F, True
   ```

   This is a proof-doc theorem surface, not a current production declaration.
   The theorem was briefly exposed as production Lean in PR #78, but that
   introduced an admitted Hall-Wightman source obligation on the active import
   path.  It is now intentionally quarantined here until it has either a
   checked proof or an explicitly approved source-import boundary.  When it
   returns to Lean, it should be an existence theorem because Lean
   declarations whose type is data are definitions, not propositions; that
   keeps the Hall-Wightman input explicit instead of hiding it in a `def`.

   Proof content:

   1. derive complex-Lorentz overlap invariance from restricted real Lorentz
      invariance using `BHW.complex_lorentz_invariance`;
   2. use `BHW.extendF_holomorphicOn` to get the single ordinary
      extended-tube continuation `BHW.extendF F`;
   3. apply Hall-Wightman Theorem I to obtain a scalar-product representative
      on `BHW.sourceExtendedTubeGramDomain d n`;
   4. use Hall-Wightman Lemma 3 to record `U_relOpen`, `U_connected`, and
      local variety holomorphicity.  For `n > d + 1`, this is relative
      holomorphicity on the rank-bounded scalar-product variety, not
      full-matrix holomorphicity.

   Packaging note: this local `SourceScalarRepresentativeData` object should
   stay tied to the ordinary extended-tube scalar image
   `sourceExtendedTubeGramDomain d n`.  The later global Hall-Wightman
   single-valuedness statement on `M_n` / `S''_n` is a separate continuation
   theorem for this branch data, not evidence that the representative itself
   should already be packaged as a globally defined object at this stage.

   The compact-test anchor must next be converted to pointwise equality on the
   real patch.  This is a standard distributional-to-pointwise step using the
   already available compact-support uniqueness theorem and continuity of
   `extendF F` on the ordinary extended tube:

   ```lean
   theorem BHW.sourceAnchor_compactBranchEq_pointwise_on_realPatch
       [NeZero d]
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (hAnchor :
         BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (π : Equiv.Perm (Fin n))
       (i : Fin n)
       (hi : i.val + 1 < n) :
       ∀ x, x ∈ hAnchor.realPatch π i hi ->
         BHW.extendF F (fun k => BHW.realEmbed x (π k)) =
           BHW.extendF F
             (fun k =>
               BHW.realEmbed x
                 ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k))
   ```

   Proof transcript:

   ```lean
     let L x := BHW.extendF F (fun k => BHW.realEmbed x (π k))
     let R x := BHW.extendF F
       (fun k =>
         BHW.realEmbed x
           ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k))
     have hL_cont : ContinuousOn L (hAnchor.realPatch π i hi) := by
       -- compose `extendF_holomorphicOn.continuousOn` with
       -- `realEmbed` and use `hAnchor.realPatch_left_sector`.
     have hR_cont : ContinuousOn R (hAnchor.realPatch π i hi) := by
       -- same, using `hAnchor.realPatch_right_sector`.
     have hEqOn : Set.EqOn L R (hAnchor.realPatch π i hi) := by
       refine SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
         (hAnchor.realPatch_open π i hi) hL_cont hR_cont ?_
       intro φ hφ_compact hφ_tsupport
       exact hAnchor.compact_branch_eq π i hi φ hφ_compact hφ_tsupport
     exact hEqOn
   ```

   The pointwise real-patch equality then becomes equality of the scalar
   representative on the anchor Gram environment:

   ```lean
   theorem BHW.sourceScalarRepresentative_adjacent_seed_eq_on_environment
       [NeZero d]
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (hRep :
         BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor :
         BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (π : Equiv.Perm (Fin n))
       (i : Fin n)
       (hi : i.val + 1 < n) :
       let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       ∀ G, G ∈ hAnchor.gramEnvironment π i hi ->
         hRep.Phi (BHW.sourceRealGramComplexify n G) =
           hRep.Phi
             (BHW.sourcePermuteComplexGram n τ
               (BHW.sourceRealGramComplexify n G))
   ```

   Proof transcript:

   ```lean
     intro τ G hG
     rcases hAnchor.gram_environment_realized π i hi G hG with
       ⟨x, hxPatch, hGx⟩
     have hpoint :=
       BHW.sourceAnchor_compactBranchEq_pointwise_on_realPatch
         (d := d) n F hF_holo hF_lorentz hAnchor π i hi x hxPatch
     have hleft_ET :
         BHW.realEmbed (fun k => x (π k)) ∈ BHW.ExtendedTube d n := by
       simpa [BHW.permutedExtendedTubeSector, BHW.realEmbed] using
         hAnchor.realPatch_left_sector π i hi x hxPatch
     have hright_ET :
         BHW.realEmbed
           (fun k => x ((π * τ) k)) ∈ BHW.ExtendedTube d n := by
       simpa [BHW.permutedExtendedTubeSector, BHW.realEmbed] using
         hAnchor.realPatch_right_sector π i hi x hxPatch
     have hleft :=
       hRep.branch_eq
         (BHW.realEmbed (fun k => x (π k))) hleft_ET
     have hright :=
       hRep.branch_eq
         (BHW.realEmbed (fun k => x ((π * τ) k))) hright_ET
     -- Rewrite the two Gram arguments by
     -- `sourceMinkowskiGram_realEmbed`,
     -- `sourceRealGramComplexify_perm`,
     -- `hAnchor.gram_right_eq_perm_left`, and `hGx`.
     calc
       hRep.Phi (BHW.sourceRealGramComplexify n G)
           = BHW.extendF F (fun k => BHW.realEmbed x (π k)) := by
             simpa [hGx, BHW.sourceMinkowskiGram_realEmbed] using hleft
       _ = BHW.extendF F
             (fun k => BHW.realEmbed x ((π * τ) k)) := hpoint
       _ = hRep.Phi
             (BHW.sourcePermuteComplexGram n τ
               (BHW.sourceRealGramComplexify n G)) := by
             have hrightGram :
                 BHW.sourceMinkowskiGram d n
                     (BHW.realEmbed (fun k => x ((π * τ) k))) =
                   BHW.sourcePermuteComplexGram n τ
                     (BHW.sourceRealGramComplexify n G) := by
               calc
                 BHW.sourceMinkowskiGram d n
                     (BHW.realEmbed (fun k => x ((π * τ) k)))
                     = BHW.sourceRealGramComplexify n
                         (BHW.sourceRealMinkowskiGram d n
                           (fun k => x ((π * τ) k))) := by
                         exact BHW.sourceMinkowskiGram_realEmbed
                           (d := d) (n := n)
                           (fun k => x ((π * τ) k))
                 _ = BHW.sourceRealGramComplexify n
                         (BHW.sourcePermuteGram n τ
                           (BHW.sourceRealMinkowskiGram d n
                             (fun k => x (π k)))) := by
                         rw [hAnchor.gram_right_eq_perm_left π i hi x hxPatch]
                 _ = BHW.sourceRealGramComplexify n
                         (BHW.sourcePermuteGram n τ G) := by
                         rw [hGx]
                 _ = BHW.sourcePermuteComplexGram n τ
                         (BHW.sourceRealGramComplexify n G) := by
                         exact BHW.sourceRealGramComplexify_perm
                           (n := n) τ G
             have hright' :
                 hRep.Phi
                     (BHW.sourcePermuteComplexGram n τ
                       (BHW.sourceRealGramComplexify n G)) =
                   BHW.extendF F
                     (fun k => BHW.realEmbed x ((π * τ) k)) := by
               simpa [hrightGram] using hright
             exact hright'.symm
   ```

   The adjacent seed equality is still only a seed.  The real
   Hall-Wightman continuation theorem consumes all adjacent seeds and extends
   them across the whole scalar-product double domain `S''_n`:

   ```lean
   theorem BHW.hallWightman_sourceScalarRepresentative_perm_invariant
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (hF_perm :
         ∀ (σ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (σ k)) = F z)
       (hRep :
         BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor :
         BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F) :
       ∀ (σ : Equiv.Perm (Fin n))
         (Z : Fin n -> Fin n -> ℂ),
         Z ∈ BHW.sourceDoublePermutationGramDomain d n σ ->
         hRep.Phi (BHW.sourcePermuteComplexGram n σ Z) =
           hRep.Phi Z
   ```

   This theorem is the formal local version of Hall-Wightman's statement that
   the symmetric `S'_n` datum has a single-valued continuation on `S''_n`.
   The proof docs no longer expose an adjacent-word induction as the endorsed
   theorem-2 route for this theorem.  The accepted contract is:

   1. use the checked adjacent seed equality theorem on each
      `hAnchor.gramEnvironment π i hi`;
   2. use Hall-Wightman real-environment uniqueness to upgrade seed equality to
      local overlap equality;
   3. use Hall-Wightman scalar-domain continuation geometry to extend from
      those local overlaps to the connected scalar-product double domains;
   4. consume the source-backed global Hall-Wightman single-valued continuation
      theorem on `S''_n` for arbitrary `σ`.

   An adjacent-word or cover-chain argument may still exist as an internal
   proof decomposition, but it is not part of the active theorem-2 contract
   unless and until it is separately formalized honestly at the scalar-domain
   level.

   Lean packaging note: the repo's existing permutation support already works
   with concrete adjacent swaps `Equiv.swap i ⟨i.val + 1, hi⟩` and the theorem
   `BHW.Fin.Perm.adjSwap_induction`.  So the proof docs should minimize use of
   an abstract predicate `IsAdjacentTransposition τ`.  The only acceptable
   abstract use is at the normalization boundary where one proves
   `τ = Equiv.swap i ⟨i.val + 1, hi⟩`; downstream theorem surfaces should then
   quantify over `(i, hi)` directly whenever possible.

   The exact local continuation helper used in step 4 should be source-facing
   and scalar-coordinate only:

   ```lean
   theorem BHW.hallWightman_scalarOverlapContinuation_from_adjacentSeeds
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_perm :
         ∀ (σ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (σ k)) = F z)
       (hRep :
         BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor :
         BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (hSeed :
         ∀ π i hi,
           let τ : Equiv.Perm (Fin n) :=
             Equiv.swap i ⟨i.val + 1, hi⟩
           ∀ G, G ∈ hAnchor.gramEnvironment π i hi ->
             hRep.Phi (BHW.sourceRealGramComplexify n G) =
               hRep.Phi
                 (BHW.sourcePermuteComplexGram n τ
                   (BHW.sourceRealGramComplexify n G))) :
       ∀ (σ : Equiv.Perm (Fin n))
         (Z : Fin n -> Fin n -> ℂ),
         Z ∈ BHW.sourceDoublePermutationGramDomain d n σ ->
         hRep.Phi (BHW.sourcePermuteComplexGram n σ Z) =
           hRep.Phi Z
   ```

   `hallWightman_scalarOverlapContinuation_from_adjacentSeeds` is the main
   remaining source-level Hall-Wightman theorem after the representative and
   real-environment suppliers are installed.  It is not an OS theorem, it must
   not mention Wightman locality, and it must not import
   `BHWPermutation.PermutationFlow`.  Because this statement compresses
   real-environment uniqueness, scalar-variety adjacent continuation, and
   adjacent-transposition word propagation, it must remain a proof-doc
   obligation until those internal steps have Lean-ready transcripts or are
   replaced by one explicitly approved source-import theorem.

   To count as implementation-ready, this compressed theorem must be treated as
   a package of three source-level sub-obligations.  The production theorem
   should not return until each of the following has its own Lean transcript or
   until a checked source import replaces the whole package.

   **(A) Real-environment uniqueness for one adjacent swap.**

   This is the Hall-Wightman/Bochner-Martin identity theorem on the
   scalar-product variety, specialized to the two functions
   `Φ` and `Z ↦ Φ (sourcePermuteComplexGram n τ Z)` on one overlap component.

   ```lean
   theorem BHW.sourceScalarRepresentative_adjacent_eq_on_overlap_of_realEnvironment
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep :
         BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor :
         BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (π : Equiv.Perm (Fin n))
       (i : Fin n)
       (hi : i.val + 1 < n)
       (data : BHW.SourceAdjacentOverlapWitness
         (d := d) n F hRep hAnchor π i hi)
       (hSeed :
         let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
         ∀ G, G ∈ hAnchor.gramEnvironment π i hi ->
           hRep.Phi (BHW.sourceRealGramComplexify n G) =
             hRep.Phi
               (BHW.sourcePermuteComplexGram n τ
                 (BHW.sourceRealGramComplexify n G))) :
       let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
       ∀ Z,
         Z ∈ data.overlap ->
           hRep.Phi (BHW.sourcePermuteComplexGram n τ Z) = hRep.Phi Z
   ```

   Here `data.overlap` is the scalar-product overlap domain attached to the
   adjacent real environment `hAnchor.gramEnvironment π i hi`.  After the
   source audit, the docs should no longer treat connectedness of the full
   adjacent double scalar-product domain as automatic.  Hall-Wightman gives
   connectedness/simply-connectedness for the global scalar domain `M_n`, but
   that does not by itself identify the adjacent double domain
   `sourceDoublePermutationGramDomain ... τ` as connected.  So the active
   internal implementation route should define the final overlap object as the
   connected component of a chosen Hall-Wightman real-environment neighbourhood
   intersected with the adjacent double scalar-product domain, containing the
   complexified real Gram environment.

   This exposes an important code-shape point: the current production constant
   `sourceAdjacentPermutationGramOverlap d n π i hi` is only a placeholder
   surface.  The final component-based overlap cannot honestly stay parameter-
   free in `(d,n,π,i,hi)` alone; it must also depend on the chosen local
   Hall-Wightman neighbourhood data, directly or through a packaged witness
   built from `hAnchor` (and possibly `hRep`).  The docs must therefore treat
   the present parameter-free constant as temporary and avoid building new API
   around it as if it were already the final mathematical object.

   The exact domain suppliers are now packaged through the production witness
   structure, rather than as a parameter-free standalone set:

   ```lean
   structure BHW.SourceAdjacentOverlapWitness
       [NeZero d]
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (π : Equiv.Perm (Fin n))
       (i : Fin n)
       (hi : i.val + 1 < n) where
     U : Set (Fin n -> Fin n -> ℂ)
     U_relOpen : BHW.IsRelOpenInSourceComplexGramVariety d n U
     overlap :
       Set (Fin n -> Fin n -> ℂ)
     overlap_relOpen :
       BHW.IsRelOpenInSourceComplexGramVariety d n overlap
     overlap_connected :
       IsConnected overlap
     overlap_subset :
       overlap ⊆
         BHW.sourceDoublePermutationGramDomain d n
             (Equiv.swap i ⟨i.val + 1, hi⟩) ∩ U
     environment_mem_overlap :
       ∀ G, G ∈ hAnchor.gramEnvironment π i hi ->
         BHW.sourceRealGramComplexify n G ∈ overlap

   -- Used directly as field projections, not as wrapper theorems:
   data.overlap_relOpen
   data.overlap_connected
   data.environment_mem_overlap
   ```

   This is the exact checked Lean surface in `SourceExtension.lean`.  The
   witness deliberately does not force a particular constructor such as
   `connectedComponentIn`; that construction belongs to the later witness
   existence theorem `(B)`.  For theorem `(A)`, the fields above are precisely
   what the identity theorem needs: relative openness, connectedness, membership
   of the real environment, and inclusion of the overlap in the adjacent double
   scalar domain.

   Source provenance:

   1. Hall-Wightman Theorem I / Lemma I supplies the scalar-product
      representative and single-valuedness on the scalar-product variety;
   2. Hall-Wightman Section 2 plus Lemma 3 supports the claims that the
      scalar-product image `M_n` is an open connected subset of the rank-bounded
      scalar-product variety and that neighbourhoods in vector space project to
      neighbourhoods in scalar-product space;
   3. the real-environment uniqueness itself is sourced by Hall-Wightman's
      discussion of real environments in Section 2;
   4. the *adjacent* overlap domain attached to one OS/Streater-Wightman real
      environment, and the finite-chain enlargement from those local overlaps
      to the whole adjacent double scalar-product domain, are repo-level
      derived specializations and must therefore be proved explicitly rather
      than cited as direct paper theorems.

   Lean proof transcript, matching the production theorem surface:

   ```lean
     dsimp
     let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
     let Ψ : (Fin n -> Fin n -> ℂ) -> ℂ :=
       fun W => hRep.Phi (BHW.sourcePermuteComplexGram n τ W)
     have hOverlap_subset_repU : data.overlap ⊆ hRep.U := by
       intro Z hZ
       have hdouble :
           Z ∈ BHW.sourceDoublePermutationGramDomain d n τ :=
         (data.overlap_subset hZ).1
       simpa [hRep.U_eq, τ] using hdouble.1
     have hPerm_overlap_subset_repU :
         data.overlap ⊆
           {Z | BHW.sourcePermuteComplexGram n τ Z ∈ hRep.U} := by
       intro Z hZ
       have hdouble :
           Z ∈ BHW.sourceDoublePermutationGramDomain d n τ :=
         (data.overlap_subset hZ).1
       simpa [hRep.U_eq, τ] using hdouble.2
     have hΦ :
         BHW.SourceVarietyHolomorphicOn d n hRep.Phi
           data.overlap := by
       exact
         BHW.SourceVarietyHolomorphicOn.of_subset_relOpen
           (d := d) (n := n) hRep.Phi_holomorphic
           data.overlap_relOpen hOverlap_subset_repU
     have hΨ :
         BHW.SourceVarietyHolomorphicOn d n Ψ
           data.overlap := by
       have hpre :
           BHW.SourceVarietyHolomorphicOn d n Ψ
             {Z | BHW.sourcePermuteComplexGram n τ Z ∈ hRep.U} := by
         simpa [Ψ] using
           BHW.SourceVarietyHolomorphicOn.precomp_sourcePermuteComplexGram
             (d := d) (n := n) hRep.Phi_holomorphic τ
       exact
         BHW.SourceVarietyHolomorphicOn.of_subset_relOpen
           (d := d) (n := n) hpre data.overlap_relOpen
           hPerm_overlap_subset_repU
     have hreal :
         ∀ G, G ∈ hAnchor.gramEnvironment π i hi ->
           hRep.Phi (BHW.sourceRealGramComplexify n G) =
             Ψ (BHW.sourceRealGramComplexify n G) := by
       intro G hG
       simpa [Ψ] using hSeed G hG
     have hEqOn :
         Set.EqOn hRep.Phi Ψ
           data.overlap :=
       (hAnchor.gramEnvironment_unique π i hi).2
         data.overlap hRep.Phi Ψ data.overlap_relOpen
         data.overlap_connected data.environment_mem_overlap
         hΦ hΨ hreal
     intro Z hZ
     exact (hEqOn hZ).symm
   ```

   The only new support lemma used here is the coordinate-permutation stability
   of source-variety holomorphy:

   ```lean
   theorem BHW.SourceVarietyHolomorphicOn.precomp_sourcePermuteComplexGram
       (hΦ : BHW.SourceVarietyHolomorphicOn d n Φ U)
       (σ : Equiv.Perm (Fin n)) :
       BHW.SourceVarietyHolomorphicOn d n
         (fun Z => Φ (BHW.sourcePermuteComplexGram n σ Z))
         {Z | BHW.sourcePermuteComplexGram n σ Z ∈ U}
   ```

   Its proof is analytic bookkeeping only: `sourcePermuteComplexGram` is a
   finite coordinate permutation, hence complex differentiable, it preserves the
   scalar-product variety by
   `sourcePermuteComplexGram_mem_sourceComplexGramVariety_iff`, and the local
   ambient holomorphic charts in `SourceVarietyHolomorphicOn` pull back along
   this map.

   **(B) Scalar-variety adjacent continuation along an overlap chain.**

   This is the step that propagates one adjacent equality from one overlap
   component to the overlap component relevant for the target `Z`.  It is pure
   Hall-Wightman continuation geometry on the scalar-product variety, not PET
   chamber bookkeeping.

   ```lean
   theorem BHW.sourceScalarRepresentative_adjacent_eq_on_doubleDomain_of_chain
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep :
         BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor :
         BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (τ : Equiv.Perm (Fin n))
       (hAdj : IsAdjacentTransposition τ)
       (hLocal :
         ∀ Z, Z ∈ BHW.sourceAdjacentSeedCover n F hRep hAnchor τ ->
           hRep.Phi (BHW.sourcePermuteComplexGram n τ Z) = hRep.Phi Z) :
       ∀ Z, Z ∈ BHW.sourceDoublePermutationGramDomain d n τ ->
         hRep.Phi (BHW.sourcePermuteComplexGram n τ Z) = hRep.Phi Z
   ```

   The following `sourceAdjacentSeedCover` package is retained as an archived
   proof-doc decomposition of the global Hall-Wightman source theorem.  It must
   not be reintroduced as production `sorry` scaffolding unless the missing
   global Hall-Wightman/Araki reachability input is first supplied explicitly.
   The active production frontier is the direct source theorem
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`.

   If this decomposition is revived after that source input is available, the
   scalar-continuation geometry should expose:

   ```lean
   def BHW.sourceAdjacentSeedCover
       [NeZero d]
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (τ : Equiv.Perm (Fin n)) :
       Set (Fin n -> Fin n -> ℂ)

   theorem BHW.sourceAdjacentPermutationGramOverlap_subset_seedCover
       [NeZero d]
       (data : BHW.SourceAdjacentOverlapWitness
         (d := d) n F hRep hAnchor π i hi) :
       data.overlap ⊆
         BHW.sourceAdjacentSeedCover n F hRep hAnchor
           (Equiv.swap i ⟨i.val + 1, hi⟩)

   theorem BHW.sourceDoublePermutationGramDomain_adjacent_chain
       [NeZero d]
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (hAdj : IsAdjacentTransposition τ)
       {Z : Fin n -> Fin n -> ℂ}
       (hZ : Z ∈ BHW.sourceDoublePermutationGramDomain d n τ) :
       ∃ (m : ℕ) (chain : Fin (m + 1) -> Fin n -> Fin n -> ℂ),
         chain 0 ∈ BHW.sourceAdjacentSeedCover n F hRep hAnchor τ ∧
         chain ⟨m, Nat.lt_succ_self m⟩ = Z ∧
         (∀ j : Fin m,
           chain ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩ ∈
               BHW.sourceAdjacentSeedCover n F hRep hAnchor τ ∧
           chain ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩ ∈
               BHW.sourceAdjacentSeedCover n F hRep hAnchor τ)
   ```

   The definition of `sourceAdjacentSeedCover` must be fixed at the same time:

   ```lean
   theorem BHW.sourceAdjacentSeedCover_eq_union
       [NeZero d]
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       {τ : Equiv.Perm (Fin n)}
       (hAdj : IsAdjacentTransposition τ) :
       ∃ (i : Fin n) (hi : i.val + 1 < n),
         τ = Equiv.swap i ⟨i.val + 1, hi⟩ ∧
         BHW.sourceAdjacentSeedCover n F hRep hAnchor τ =
           ⋃ π : Equiv.Perm (Fin n),
             {Z |
               ∃ data : BHW.SourceAdjacentOverlapWitness
                 (d := d) n F hRep hAnchor π i hi,
                 Z ∈ data.overlap}

   def BHW.sourceAdjacentOverlapLabelSet
       [NeZero d]
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (i : Fin n)
       (hi : i.val + 1 < n) :
       Set (Equiv.Perm (Fin n)) :=
     {π | ∃ data : BHW.SourceAdjacentOverlapWitness
         (d := d) n F hRep hAnchor π i hi,
         data.overlap.Nonempty}
   ```

   In the archived decomposition, the two suppliers hidden inside that theorem
   would be:

   ```lean
   theorem BHW.sourceAdjacentSeedCover_cover_doubleDomain
       [NeZero d]
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (hAdj : IsAdjacentTransposition τ) :
       BHW.sourceDoublePermutationGramDomain d n τ ⊆
         BHW.sourceAdjacentSeedCover n F hRep hAnchor τ
   ```

   The genuinely load-bearing theorem behind this cover-reaching statement
   would be the witness construction:

   ```lean
   theorem BHW.exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain
       [NeZero d]
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (i : Fin n)
       (hi : i.val + 1 < n)
       {Z : Fin n -> Fin n -> ℂ}
       (hZ :
         Z ∈ BHW.sourceDoublePermutationGramDomain d n
           (Equiv.swap i ⟨i.val + 1, hi⟩)) :
       ∃ (π : Equiv.Perm (Fin n))
         (data : BHW.SourceAdjacentOverlapWitness
           (d := d) n F hRep hAnchor π i hi),
         Z ∈ data.overlap
   ```

   Then `sourceAdjacentSeedCover_cover_doubleDomain` would be the one-line
   corollary that packages this witness into the seed cover.

   After closing `(A)`, the exact status of `(B)` is sharper:
   `exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain` is mechanical only
   if the proof first supplies one of the following honest source-domain inputs.
   Without such an input it is a source theorem in disguise, which is why it has
   been retired from production Lean.

   Preferred direct input:

   ```lean
   theorem BHW.sourceDoublePermutationGramDomain_adjacent_isConnected
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (i : Fin n)
       (hi : i.val + 1 < n) :
       IsConnected
         (BHW.sourceDoublePermutationGramDomain d n
           (Equiv.swap i ⟨i.val + 1, hi⟩))
   ```

   With this theorem, the witness construction is no longer mysterious.  For any
   fixed anchor label `π`, define

   ```lean
   U :=
     hRep.U ∩
       {Z | BHW.sourcePermuteComplexGram n
          (Equiv.swap i ⟨i.val + 1, hi⟩) Z ∈ hRep.U}

   overlap :=
     BHW.sourceDoublePermutationGramDomain d n
       (Equiv.swap i ⟨i.val + 1, hi⟩)
   ```

   Then:

   1. `U_relOpen` follows from `hRep.U_relOpen`,
      `IsRelOpenInSourceComplexGramVariety.preimage_sourcePermuteComplexGram`,
      and intersection;
   2. `overlap_relOpen` follows from
      `sourceDoublePermutationGramDomain_relOpen_of_sourceExtendedTubeGramDomain`
      and `hRep.U_eq`;
   3. `overlap_connected` is the new theorem above;
   4. `overlap_subset` is by unfolding `sourceDoublePermutationGramDomain`,
      `U`, and `hRep.U_eq`;
   5. `environment_mem_overlap` is the checked theorem
      `sourceRealGramComplexify_mem_sourceDoublePermutationGramDomain_of_environment`.

   This gives the Lean transcript:

   ```lean
     let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
     refine ⟨(1 : Equiv.Perm (Fin n)), ?data, hZ⟩
     refine
       { U := hRep.U ∩ {Z | BHW.sourcePermuteComplexGram n τ Z ∈ hRep.U}
         U_relOpen := ?hU_rel
         overlap := BHW.sourceDoublePermutationGramDomain d n τ
         overlap_relOpen := ?hOverlap_rel
         overlap_connected :=
           BHW.sourceDoublePermutationGramDomain_adjacent_isConnected
             (d := d) hd n i hi
         overlap_subset := ?hsubset
         environment_mem_overlap := ?henv }
   ```

   This is the only currently visible route that would make the generic witness
   theorem true for an arbitrary `SourceDistributionalAdjacentTubeAnchor`: it
   does not require the anchor itself to cover all components, because the whole
   adjacent double scalar domain is one connected overlap.

   The API-backed Deep Research theorem-shape check for this exact statement
   completed with the same verdict: the witness theorem is too strong from an
   arbitrary `SourceDistributionalAdjacentTubeAnchor` alone, but becomes a sound
   decomposition if supplied by a genuine global Hall-Wightman/Araki
   connectedness or source single-valuedness theorem.  Therefore the production
   route now uses the direct source-backed Hall-Wightman single-valuedness
   theorem on `S''_n`, namely
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
   as the explicit remaining analytic input.

   ```text
   v1_ChdYZXp1YWRLRUJZMjlzT0lQa1BtbXlRNBIXWGV6dWFkS0VCWTI5c09JUGtQbW15UTQ
   ```

   Unfolded at the normalized adjacent swap, this means:

   ```lean
   theorem BHW.mem_sourceAdjacentSeedCover_of_mem_doubleDomain
       [NeZero d]
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (i : Fin n)
       (hi : i.val + 1 < n)
       {Z : Fin n -> Fin n -> ℂ}
       (hZ :
         Z ∈ BHW.sourceDoublePermutationGramDomain d n
           (Equiv.swap i ⟨i.val + 1, hi⟩)) :
       Z ∈ BHW.sourceAdjacentSeedCover n F hRep hAnchor
         (Equiv.swap i ⟨i.val + 1, hi⟩)
   ```

   If the archived witness decomposition is later revived, this is the first
   theorem where the docs must stop saying merely "Hall-Wightman gives local
   scalar neighbourhoods" and instead explain how those neighbourhoods are
   chosen so that every point of the adjacent double scalar-product domain lies
   in one of the overlap components indexed by `π`.  Its source-facing proof
   route would be:

   1. realize both `Z` and `τ · Z` by ordinary extended-tube configurations,
      via the checked supplier
      `exists_sourceExtendedTube_realizations_of_mem_doubleDomain`;
   2. choose Hall-Wightman real-environment neighbourhoods around the relevant
      real boundary data for those realizations.  For this step to be honestly
      implementation-ready, the proof docs must treat it as the following
      concrete subproblem rather than one blurred sentence:
      - start from the two extended-tube realizations supplied by step 1;
      - identify the real boundary/Jost data whose Gram image is the anchor
        seed to be compared;
      - select one scalar-variety neighbourhood `U` around that real Gram
        data on which Hall-Wightman uniqueness applies;
      - prove `U` is relatively open in the source Gram variety;
      - prove the chosen anchor real-environment Gram set lies inside `U`;
      - intersect `U` with the normalized adjacent double scalar domain and
        take the connected component containing the anchor Gram environment.
   3. normalize the adjacent transposition to `Equiv.swap i ⟨i+1⟩`;
   4. show one permutation label `π` places the chosen local real environment
      into the anchor family `hAnchor.gramEnvironment π i hi`;
   5. build `data : SourceAdjacentOverlapWitness ... π i hi` from that chosen
      local real-environment neighbourhood and component;
   6. conclude that `Z ∈ data.overlap`.

   The seed-cover membership theorem is then just:

   7. insert the witness `(π, data)` into the existential definition of
      `sourceAdjacentSeedCover`.

   The first is the honest scalar-domain reachability theorem.  The second is
   now best treated by reusing mathlib's
   `IsConnected.biUnion_of_reflTransGen` rather than introducing a bespoke
   finite-open-cover theorem: once the overlap components are individually
   connected and their index graph is `ReflTransGen`-connected via nonempty
   intersections, mathlib already supplies connectedness of their union.  Then
   `sourceDoublePermutationGramDomain_adjacent_chain` is obtained by combining
   cover-reaching with the `ReflTransGen`-connected union of overlap
   components, and finally extracting an explicit finite list witness from the
   `ReflTransGen` proof only at the very end if a concrete chain datatype is
   still needed by the downstream permutation-induction API.

   So the overlap-index connectivity theorem should be recorded explicitly as:

   ```lean
   theorem BHW.sourceAdjacentOverlapIndex_reflTransGen
       [NeZero d]
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       (i : Fin n)
       (hi : i.val + 1 < n) :
       ∀ π₁ ∈ BHW.sourceAdjacentOverlapLabelSet n F hRep hAnchor i hi,
         ∀ π₂ ∈ BHW.sourceAdjacentOverlapLabelSet n F hRep hAnchor i hi,
         ReflTransGen
           (fun a b : Equiv.Perm (Fin n) =>
             ∃ dataa : BHW.SourceAdjacentOverlapWitness
                 (d := d) n F hRep hAnchor a i hi,
               ∃ datab : BHW.SourceAdjacentOverlapWitness
                 (d := d) n F hRep hAnchor b i hi,
                 (dataa.overlap ∩ datab.overlap).Nonempty)
           π₁ π₂
   ```

   This restricted label set is the right theorem surface for the current
   route: it talks only about overlap components that actually occur.  What is
   not acceptable is to leave the connected-union step as unnamed prose.

   The intended proof transcript is:

   1. use `sourceAdjacentSeedCover_eq_union` to rewrite the seed cover as a
      union of overlap components indexed by `sourceAdjacentOverlapLabelSet`;
   2. prove each overlap component in that label set is connected by the
      witness field `data.overlap_connected`;
   3. use Hall-Wightman/source-side reachability to show the seed cover is
      connected as a subset of the adjacent double scalar-product domain;
   4. apply the contrapositive of disconnected unions: if two active labels
      were not related by `ReflTransGen` through nonempty intersections, the
      union would split into two disjoint relatively open subunions, violating
      connectedness of the seed cover;
   5. feed the resulting `ReflTransGen` witness to
      `IsConnected.biUnion_of_reflTransGen`.

   This is a genuine topological lemma about the chosen cover, not new QFT
   content, but it must still be written down explicitly because the later
   permutation-induction API depends on an actual chain of overlap components.

   The chain theorem is intentionally phrased in scalar-product language only.
   If the eventual proof uses Hall-Wightman Lemma 3 in a stronger way, the
   stronger theorem must still be stated at this scalar-domain level.
   This is the first place where the docs now deliberately leave the realm of
   direct source quotation: Hall-Wightman gives connectedness/simply-connected
   scalar-product geometry for the global scalar domain, but the adjacent seed
   cover, cover-reaching theorem, and finite-chain extraction are derived
   specializations needed for the Lean
   route.  They must be justified from the source geometry, not merely named.

   Lean proof transcript:

   ```lean
     intro Z hZ
     obtain ⟨m, chain, hchain0, hchainZ, hstep⟩ :=
       BHW.sourceDoublePermutationGramDomain_adjacent_chain
         (d := d) (n := n) τ hAdj Z hZ
     have hprop :
         ∀ j : Fin (m + 1),
           hRep.Phi (BHW.sourcePermuteComplexGram n τ (chain j)) =
             hRep.Phi (chain j) := by
       intro j
       -- induct along the overlap chain using `hLocal` on each component
     simpa [hchainZ] using
       hprop ⟨m, Nat.lt_succ_self m⟩
   ```

   The only acceptable hidden supplier here is a scalar-product-domain chain
   theorem extracted from Hall-Wightman Lemma 3 / Section 2.  It must not
   smuggle back in `PermutationFlow`, fixed-`w` chamber galleries, or any
   locality-dependent theorem.  On the current route this chain layer is live
   internal source geometry, not optional decoration.

   **(C) Propagation from adjacent steps to a general permutation.**

   After the correction above, this is no longer “pure algebra.”  The passage
   from adjacent transpositions to a general permutation needs both:

   1. permutation algebra (`sourcePermuteComplexGram_mul` and an adjacent-word
      decomposition of `σ`), and
   2. an admissible chain of intermediate scalar points showing that the
      adjacent invariance theorem may be applied step by step on the relevant
      double domains.

   So the theorem must be documented as a word-chain propagation theorem, not
   as a naked group-theoretic corollary.

   **Route decision.**

   At this point the proof docs should no longer treat this word-chain route as
   the endorsed theorem-2 implementation path.  Hall-Wightman's paper gives a
   global single-valued continuation theorem on the scalar-product domain
   `M_n`/`S''_n`; it does not advertise a separate adjacent-word induction on
   permutation generators.  The adjacent-word package below is therefore best
   understood as a possible internal decomposition of the Hall-Wightman source
   theorem, not as a theorem-2 contract in its own right.

   The active route is:

   1. keep (A) as the local real-environment uniqueness theorem;
   2. keep (B) as source-facing Hall-Wightman adjacent continuation geometry,
      but do not implement the overlap-component / seed-cover / reachability
      package as production `sorry` scaffolding unless its global source input
      is supplied explicitly;
   3. treat the passage from adjacent seeds to arbitrary `σ` as the direct
      Hall-Wightman single-valued continuation theorem on the connected
      scalar-product double domain, unless and until a fully honest scalar-word
      theorem is actually proved.

   In particular, the proof-doc target is now split cleanly into two stages:

   1. a local Hall-Wightman scalar representative on the ordinary
      extended-tube scalar image (`SourceScalarRepresentativeData`), and
   2. a separate global continuation theorem transporting that branch across
      the connected double scalar-product domain.

   This is faithful to the source and avoids the false pressure to globalize
   `SourceScalarRepresentativeData` itself.

   In particular, the theorem names
   `sourceScalarRepresentative_permInvariant_of_adjacentGenerators`,
   `SourcePermutationWordChain`, and
   `sourcePermutationWordChain_of_mem_doubleDomain`
   should remain quarantined in the proof docs.  They are no longer part of
   the endorsed immediate implementation target for theorem 2.

   ```lean
   theorem BHW.sourceScalarRepresentative_permInvariant_of_adjacentGenerators
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAdj :
         ∀ τ : Equiv.Perm (Fin n),
           IsAdjacentTransposition τ ->
           ∀ Z, Z ∈ BHW.sourceDoublePermutationGramDomain d n τ ->
             hRep.Phi (BHW.sourcePermuteComplexGram n τ Z) = hRep.Phi Z) :
       ∀ σ : Equiv.Perm (Fin n),
         ∀ Z, Z ∈ BHW.sourceDoublePermutationGramDomain d n σ ->
           hRep.Phi (BHW.sourcePermuteComplexGram n σ Z) = hRep.Phi Z
   ```

   Lean proof transcript:

   ```lean
     intro σ Z hZ
     let hChain :=
       BHW.sourcePermutationWordChain_of_mem_doubleDomain
         (d := d) (n := n) hZ
     induction hChain.word generalizing Z with
     | nil =>
         simpa using rfl
     | cons step rest ih =>
         have hstep :
             hRep.Phi
                 (BHW.sourcePermuteComplexGram n step (hChain.chain 0)) =
               hRep.Phi (hChain.chain 0) :=
           hAdj step ?hstep_adj (hChain.chain 0) ?hstep_mem
         have hrest :
             hRep.Phi
                 (BHW.sourcePermuteComplexGram n
                   (rest.foldr (· * ·) 1)
                   (hChain.chain 1)) =
               hRep.Phi (hChain.chain 1) :=
           ih ?hrest_chain
         -- rewrite the nested permutation action into multiplication order and
         -- identify the endpoint with `hChain.chain_last`
         simpa [BHW.sourcePermuteComplexGram_mul] using hrest.trans hstep
   ```

   The domain-membership lemmas `hstep_mem` and `hrest_mem` are not mere
   bookkeeping: they are the exact place where the scalar-product double-domain
   geometry for a permutation word must be stated.  In fact, the naive
   `mul_mem_left/right` route is too optimistic: from
   `Z ∈ BHW.sourceDoublePermutationGramDomain d n (α * β)` one does not
   automatically get either `Z ∈ BHW.sourceDoublePermutationGramDomain d n α`
   or `BHW.sourcePermuteComplexGram n α Z ∈
   BHW.sourceDoublePermutationGramDomain d n β`, because the ordinary extended
   tube is not permutation-invariant.  So the proof doc must not rely on those
   statements as if they were formal consequences of the current domain
   definition.

   If one insists on the adjacent-word internal decomposition anyway, the
   minimum algebra/geometry supplier package would be:

   ```lean
   theorem BHW.sourcePermuteComplexGram_mul
       (n : ℕ)
       (α β : Equiv.Perm (Fin n))
       (Z : Fin n -> Fin n -> ℂ) :
       BHW.sourcePermuteComplexGram n (α * β) Z =
         BHW.sourcePermuteComplexGram n β
           (BHW.sourcePermuteComplexGram n α Z)

   theorem BHW.perm_word_of_adjacent_transpositions
       (n : ℕ)
       (σ : Equiv.Perm (Fin n)) :
       ∃ word : List (Equiv.Perm (Fin n)),
         (∀ τ ∈ word, IsAdjacentTransposition τ) ∧
         word.foldr (· * ·) 1 = σ

   structure BHW.SourcePermutationWordChain
       (d n : ℕ)
       (σ : Equiv.Perm (Fin n))
       (Z : Fin n -> Fin n -> ℂ) where
     word : List (Equiv.Perm (Fin n))
     word_adj :
       ∀ τ ∈ word, IsAdjacentTransposition τ
     word_eval :
       word.foldr (· * ·) 1 = σ
     chain :
       Fin (word.length + 1) -> Fin n -> Fin n -> ℂ
     chain_zero :
       chain 0 = Z
     chain_last :
       chain ⟨word.length, Nat.lt_succ_self word.length⟩ =
         BHW.sourcePermuteComplexGram n σ Z
     step_mem :
       ∀ j : Fin word.length,
         chain ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩ ∈
             BHW.sourceDoublePermutationGramDomain d n (word.get j) ∧
         chain ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩ =
           BHW.sourcePermuteComplexGram n (word.get j)
             (chain ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩)

   theorem BHW.sourcePermutationWordChain_of_mem_doubleDomain
       [NeZero d]
       {σ : Equiv.Perm (Fin n)}
       {Z : Fin n -> Fin n -> ℂ}
       (hZ : Z ∈ BHW.sourceDoublePermutationGramDomain d n σ) :
       BHW.SourcePermutationWordChain d n σ Z
   ```

   There is one more theorem surface that must be fixed before this package is
   truly implementation-ready: the normalization of an abstract adjacent
   transposition into the concrete swap index used by the OS anchor.

   ```lean
   theorem BHW.exists_adjacentSwapIndex
       (n : ℕ)
       {τ : Equiv.Perm (Fin n)}
       (hAdj : IsAdjacentTransposition τ) :
       ∃ (i : Fin n) (hi : i.val + 1 < n),
         τ = Equiv.swap i ⟨i.val + 1, hi⟩
   ```

   The seed-cover definition should then commit to the corresponding union over
   permutation labels `π`:

   ```lean
   theorem BHW.sourceAdjacentSeedCover_eq_union
       [NeZero d]
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hRep : BHW.SourceScalarRepresentativeData (d := d) n F)
       (hAnchor : BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F)
       {τ : Equiv.Perm (Fin n)}
       (hAdj : IsAdjacentTransposition τ) :
       ∃ (i : Fin n) (hi : i.val + 1 < n),
         τ = Equiv.swap i ⟨i.val + 1, hi⟩ ∧
         BHW.sourceAdjacentSeedCover n F hRep hAnchor τ =
           ⋃ π : Equiv.Perm (Fin n),
             {Z |
               ∃ data : BHW.SourceAdjacentOverlapWitness
                 (d := d) n F hRep hAnchor π i hi,
                 Z ∈ data.overlap}
   ```

   This is not cosmetic bookkeeping.  Without it, the final wrapper still hides
   the step from an abstract adjacent generator `τ` to the concrete
   Hall-Wightman real environment data stored by
   `SourceDistributionalAdjacentTubeAnchor`.

   These suppliers are now mathematically scoped tightly enough that the
   blueprint can state how each one should be proved, rather than merely
   naming it.

   **Proof plan for the derived scalar-geometry suppliers.**

   1. `data.overlap` for `data : SourceAdjacentOverlapWitness`:
      active definition:
      packaged by `SourceAdjacentOverlapWitness`; concretely, the overlap is
      the connected component of
      `sourceDoublePermutationGramDomain d n τ ∩ U`, where `U` is the
      scalar-variety neighbourhood supplied by the real-environment theorem,
      containing the complexified real Gram image of the adjacent seed.
      Optional later simplification:
      if a separate theorem really proves the whole adjacent double domain is
      already the needed connected neighbourhood, then this definition may be
      collapsed to `sourceDoublePermutationGramDomain d n τ`.
   2. `SourceAdjacentOverlapWitness.overlap_relOpen`:
      archived route: deduce relative openness because both pieces in the
      intersection are relatively open in the scalar-product variety:
      `sourceDoublePermutationGramDomain` is open by its defining inequalities,
      and `U` is relatively open by the Hall-Wightman real-environment
      theorem.  Then pass to the chosen connected component of a relatively
      open subset.
   3. `SourceAdjacentOverlapWitness.overlap_connected`:
      archived route: immediate from the definition as a connected component.
      A direct full-domain connectedness proof would be a later optimization,
      not current source-gate input.

      The exact Lean surface is a structure field, not a wrapper theorem:

      ```lean
      data.overlap_connected : IsConnected data.overlap
      ```

      This field is no longer the live mathematical blocker.  The later
      enlargement from these seed overlap components to the full adjacent
      double scalar-product domain is an archived source-theorem decomposition,
      not a production target unless its global source input is supplied.
   4. `gramEnvironment_complexify_mem_adjacentOverlap`:
      show that each real Gram point in
      `hAnchor.gramEnvironment π i hi` lies in the Hall-Wightman neighbourhood
      `U` by construction, and lies in the adjacent double scalar-product
      domain because the same real configuration is admissible for both the
      identity and adjacent-permuted source orderings.  Then the distinguished
      component condition is satisfied by definition of the overlap component.
   5. `sourceAdjacentSeedCover`:
      archived route. Define it as the union of all adjacent overlap components
      associated to the same adjacent transposition `τ`.
   6. `sourceAdjacentPermutationGramOverlap_subset_seedCover`:
      archived route, tautological from the union definition of the seed cover.
   7. `sourceDoublePermutationGramDomain_adjacent_chain`:
      archived scalar-geometry decomposition.  If revived, it must use the
      source-backed global Hall-Wightman geometry on `M_n` / `S''_n` together
      with the repo-level adjacent overlap cover to show that every point of
      the adjacent double scalar-product domain is reached by a finite chain of
      overlap components beginning at a component containing a real-environment
      seed point.  The finite-chain extraction itself is standard topology; the
      nontrivial content is that the chosen overlap cover really reaches the
      entire adjacent double domain.  This is why the theorem has been retired
      from production and replaced by the direct source frontier.

   **Important correction about the tempting vector-overlap shortcut.**

   It is not enough to observe that the repo already proves connectedness of
   the vector-valued adjacent overlap domain
   `adjSwapExtendedOverlapSet d n i hi` and then try to transfer that
   connectedness to
   `sourceDoublePermutationGramDomain d n (Equiv.swap i ⟨i.val + 1, hi⟩)` by a
   Gram-map image theorem.  The reason is structural:

   - `adjSwapExtendedOverlapSet` asks for one complex configuration `w` such
     that both `w` and `w ∘ τ` lie in `ExtendedTube`;
   - `sourceDoublePermutationGramDomain` asks only that `Z` and `τ·Z` each
     occur as Gram matrices of *some* extended-tube configurations, not
     necessarily the same configuration and its permute.

   So the naive equality

   ```lean
   sourceDoublePermutationGramDomain d n τ =
     sourceMinkowskiGram d n '' adjSwapExtendedOverlapSet d n i hi
   ```

   is not justified and should not be used in the proof docs.  Any transfer of
   connectedness from vector overlap to scalar-product overlap would need an
   additional Hall-Wightman theorem saying that whenever `Z` and `τ·Z` are both
   realized in the extended tube, they may be realized by one common
   configuration orbit in the required overlap domain.  That theorem is not
   currently part of the approved route.

   A related tempting symmetry shortcut is also invalid: the scalar
   double-domain is not obviously equivariant under simultaneous conjugation of
   the permutation parameter and the Gram coordinates, because
   `sourceExtendedTubeGramDomain` itself is not permutation-invariant.  So the
   docs must not assume a theorem of the form

   ```lean
   sourcePermuteComplexGram n α Z ∈
     sourceDoublePermutationGramDomain d n (α * σ * α⁻¹) ↔
   Z ∈ sourceDoublePermutationGramDomain d n σ
   ```

   unless that statement is separately proved from stronger source geometry.
   8. `sourcePermuteComplexGram_mul`:
      prove by direct index calculation from the definition of
      `sourcePermuteComplexGram`; this is purely algebraic and should be
      discharged before any analytic continuation work resumes.
   9. `perm_word_of_adjacent_transpositions`:
      import or prove the standard Coxeter-generation fact for `Fin n`
      permutations.  This remains a finite-group lemma, but it is only one
      input to the corrected step (C), not the whole theorem.
   10. `exists_adjacentSwapIndex` and
       `sourceAdjacentSeedCover_eq_union`:
       the first is pure finite permutation combinatorics; the second is the
       bridge from that combinatorics to the checked anchor API.  The proof of
       the second should be by unfolding the definition of
       `sourceAdjacentSeedCover` after normalizing `τ` to
       `Equiv.swap i ⟨i.val + 1, hi⟩`; no new analytic content should appear
       here.
   11. `SourcePermutationWordChain` and
       `sourcePermutationWordChain_of_mem_doubleDomain`:
       these replace the false naive `mul_mem_left/right` route.  The required
       content is not “membership descends automatically along a product,” but
       “for each `Z` admissible for `σ`, choose an adjacent-transposition word
       and an accompanying chain of intermediate scalar points such that each
       step is admissible for the next adjacent transposition.”  This is the
       genuine geometry/combinatorics supplier that the induction proof of (C)
       needs.

   But the active blueprint should now assume the opposite default: unless this
   word-chain package is separately justified in full detail, the docs should
   retreat to the stronger global Hall-Wightman continuation theorem rather
   than force a bad local induction.

   If the implementation needs a different left/right orientation for the word
   recursion, the docs must fix that orientation before the Lean pass begins.
   This entire package is derived algebra/geometry rather than a paper theorem:
   the paper gives the single-valued continuation result, while the Lean route
   decomposes its use into adjacent generators plus domain-membership
   bookkeeping.  That decomposition is allowed, but only if these exact
   membership lemmas are treated as genuine proof obligations.

   Accordingly, the endorsed source theorem surface is still the global one:

   ```lean
   theorem BHW.hallWightman_scalarOverlapContinuation_from_adjacentSeeds
       ... :
       ∀ (σ : Equiv.Perm (Fin n))
         (Z : Fin n -> Fin n -> ℂ),
         Z ∈ BHW.sourceDoublePermutationGramDomain d n σ ->
         hRep.Phi (BHW.sourcePermuteComplexGram n σ Z) = hRep.Phi Z
   ```

   Its accepted proof transcript is now:

   1. for each adjacent real environment `hAnchor.gramEnvironment π i hi`, use
      the checked seed equality theorem plus Hall-Wightman uniqueness to obtain
      equality on the corresponding local overlap component (step (A));
   2. use the Hall-Wightman scalar-domain continuation geometry to enlarge
      those local equalities to the connected adjacent double domains (step
      (B));
   3. invoke the source-backed Hall-Wightman single-valued continuation theorem
      on the connected scalar-product double domain for arbitrary `σ`, rather
      than inserting an unproved local word-induction theorem;
   4. close the PET branch-compatibility theorem from that global source
      equality.

   This is the unique endorsed route.  The adjacent-word package is retained
   below only as an archived possible internal decomposition, not as a live
   theorem-2 contract.

   Once the source scalar representative theorem and the direct global
   Hall-Wightman scalar invariance theorem are supplied, the PET-sector
   compatibility step has a short Lean proof:

   ```lean
   private theorem hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (hF_perm :
         ∀ (σ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (σ k)) = F z)
       (hAnchor :
         BHW.SourceDistributionalAdjacentTubeAnchor (d := d) n F) :
       ∀ (π ρ : Equiv.Perm (Fin n))
         (z : Fin n -> Fin (d + 1) -> ℂ),
         z ∈ BHW.permutedExtendedTubeSector d n π ->
         z ∈ BHW.permutedExtendedTubeSector d n ρ ->
         BHW.extendF F (fun k => z (π k)) =
           BHW.extendF F (fun k => z (ρ k)) := by
     intro π ρ z hzπ hzρ
     let σ : Equiv.Perm (Fin n) := π.symm * ρ
     let w : Fin n -> Fin (d + 1) -> ℂ := fun k => z (π k)
     have hw : w ∈ BHW.ExtendedTube d n := by
       simpa [w, BHW.permutedExtendedTubeSector] using hzπ
     have hσw : (fun k => w (σ k)) ∈ BHW.ExtendedTube d n := by
       simpa [w, σ, Equiv.Perm.mul_apply,
         BHW.permutedExtendedTubeSector] using hzρ
     let Z : Fin n -> Fin n -> ℂ := BHW.sourceMinkowskiGram d n w
     have hZ : Z ∈ BHW.sourceDoublePermutationGramDomain d n σ := by
       refine ⟨?_, ?_⟩
       · exact ⟨w, hw, rfl⟩
       · rw [← BHW.sourceMinkowskiGram_perm (d := d) (n := n) σ w]
         exact ⟨fun k => w (σ k), hσw, rfl⟩
     obtain ⟨hRep, _⟩ :=
       BHW.hallWightman_exists_sourceScalarRepresentative_of_forwardTube_lorentz
         (d := d) hd n F hF_holo hF_lorentz
     have hperm :
         hRep.Phi (BHW.sourcePermuteComplexGram n σ Z) =
           hRep.Phi Z :=
       BHW.hallWightman_sourceScalarRepresentative_perm_invariant
         (d := d) hd n F hF_holo hF_lorentz hF_perm hRep hAnchor
         σ Z hZ
     have hleft :
         hRep.Phi Z = BHW.extendF F (fun k => z (π k)) := by
       simpa [Z, w] using hRep.branch_eq w hw
     have hright :
         hRep.Phi (BHW.sourcePermuteComplexGram n σ Z) =
           BHW.extendF F (fun k => z (ρ k)) := by
       rw [← BHW.sourceMinkowskiGram_perm (d := d) (n := n) σ w]
       simpa [w, σ, Equiv.Perm.mul_apply] using
         hRep.branch_eq (fun k => w (σ k)) hσw
     exact hleft.symm.trans (hperm.symm.trans hright)
   ```

   The wrapper theorem
   `hallWightman_source_permutedBranch_compatibility`, if kept as a separate
   name, then closes by pure sector bookkeeping:

   ```lean
   private theorem hallWightman_source_permutedBranch_compatibility
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (hF_perm :
         ∀ (σ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (σ k)) = F z)
       (hAnchor :
         SourceDistributionalAdjacentTubeAnchor (d := d) n F) :
       ∀ (π ρ : Equiv.Perm (Fin n))
         (z : Fin n -> Fin (d + 1) -> ℂ),
         z ∈ BHW.permutedExtendedTubeSector d n π ->
         z ∈ BHW.permutedExtendedTubeSector d n ρ ->
         BHW.extendF F (fun k => z (π k)) =
           BHW.extendF F (fun k => z (ρ k)) := by
     intro π ρ z hzπ hzρ
     exact
       hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor
         (d := d) hd n F hF_holo hF_lorentz hF_perm hAnchor
         π ρ z hzπ hzρ
   ```

   Consequence for the current Lean surface: the generic BHW branch-law,
   extension, and sector-equality theorems now carry
   `SourceDistributionalAdjacentTubeAnchor` explicitly.  The subsequent
   PET-gluing code remains the correct mechanical consumer.  The remaining
   hard work is to supply the direct Hall-Wightman source theorem and construct
   the OS-specific anchor for `bvt_F` from the OS-II Schwinger/edge data.

5. **Final theorem proof after source-surface correction.**

   The public branch-law theorem now carries the
   distributional Euclidean/Jost anchor package from item 4.  It may later be
   replaced later by an OS-specific theorem that supplies that package
   internally.  Its generic proof is mechanical: construct the elementary
   `S'_n` branch facts, apply the distributional source compatibility theorem,
   and then use the existing `BHW.gluedPETValue` API to build the single
   `Fpet`.

   Immediate Lean proof transcript for the generic distributional-anchor
   version:

   ```lean
   theorem BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry
       [NeZero d]
       (hd : 2 <= d)
       (n : ℕ)
       (F : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ)
       (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
       (hF_lorentz :
         ∀ (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.ForwardTube d n ->
           F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
       (hF_perm :
         ∀ (σ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (σ k)) = F z)
       (hAnchor :
         SourceDistributionalAdjacentTubeAnchor (d := d) n F) :
       ∃ Fpet : (Fin n -> Fin (d + 1) -> ℂ) -> ℂ,
         DifferentiableOn ℂ Fpet (BHW.PermutedExtendedTube d n) ∧
         ∀ (π : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.permutedExtendedTubeSector d n π ->
           Fpet z = BHW.extendF F (fun k => z (π k)) := by
     let G : (π : Equiv.Perm (Fin n)) ->
         (Fin n -> Fin (d + 1) -> ℂ) -> ℂ :=
       fun π z => BHW.extendF F (fun k => z (π k))

     have hGpft_holo :
         ∀ π, DifferentiableOn ℂ
           (fun z : Fin n -> Fin (d + 1) -> ℂ => F (fun k => z (π k)))
           (BHW.PermutedForwardTube d n π) :=
       fun π =>
         source_permutedForwardBranch_holomorphicOn
           (d := d) (n := n) F hF_holo π

     have hGpft_lorentz :
         ∀ π (Λ : RestrictedLorentzGroup d)
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.PermutedForwardTube d n π ->
           (fun z' : Fin n -> Fin (d + 1) -> ℂ =>
               F (fun k => z' (π k)))
             (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z) =
           F (fun k => z (π k)) :=
       fun π =>
         source_permutedForwardBranch_restrictedLorentzInvariant
           (d := d) (n := n) F hF_lorentz π

     have hGpft_symm :
         ∀ π ρ (z : Fin n -> Fin (d + 1) -> ℂ),
           F (fun k => z (π k)) = F (fun k => z (ρ k)) :=
       source_permutedForwardBranch_symmetric
         (d := d) (n := n) F hF_perm

     have hG_holo :
         ∀ π, DifferentiableOn ℂ (G π)
           (BHW.permutedExtendedTubeSector d n π) :=
       fun π =>
         BHW.permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz
           (d := d) n F hF_holo hF_lorentz π

     have hcompat :
         ∀ (π ρ : Equiv.Perm (Fin n))
           (z : Fin n -> Fin (d + 1) -> ℂ),
           z ∈ BHW.permutedExtendedTubeSector d n π ->
           z ∈ BHW.permutedExtendedTubeSector d n ρ ->
           G π z = G ρ z :=
       hallWightman_source_permutedBranch_compatibility
         (d := d) hd n F hF_holo hF_lorentz hF_perm hAnchor

     refine ⟨BHW.gluedPETValue (d := d) (n := n) G, ?_, ?_⟩
     · exact BHW.gluedPETValue_holomorphicOn
         (d := d) (n := n) G hG_holo hcompat
     · intro π z hzπ
       exact BHW.gluedPETValue_eq_of_mem_sector
         (d := d) (n := n) G hcompat π z hzπ
   ```

   The variables `hGpft_holo`, `hGpft_lorentz`, and `hGpft_symm` are written
   in the transcript to make the formal `S'_n` datum explicit.  The
   `hGpft_symm` line is not the mathematical anchor by itself; the anchor is
   the distributional compact-test package `hAnchor`.  If Lean reports the
   elementary datum facts unused in the final proof of the public theorem,
   they should be moved into the proof of
   `hallWightman_source_permutedBranch_compatibility`, not deleted from the
   mathematical proof plan.

   The theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` must remain a
   downstream consumer.

The OS-specific Slot-6 theorem is then only the specialization to the selected
OS-II-corrected witness:

```lean
theorem bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (d + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π ->
      z ∈ BHW.permutedExtendedTubeSector d n ρ ->
      bvt_selectedPETBranch (d := d) OS lgc n π z =
        bvt_selectedPETBranch (d := d) OS lgc n ρ z
```

Lean-shaped specialization proof after the distributional anchor package is
supplied from the OS-II construction:

```lean
  intro π ρ z hzπ hzρ
  have hAnchor :
      SourceDistributionalAdjacentTubeAnchor
        (d := d) n (bvt_F OS lgc n) :=
    bvt_F_distributionalJostAnchor_of_OSII
      (d := d) hd OS lgc n
  simpa [bvt_selectedPETBranch] using
    BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry
      (d := d) hd n (bvt_F OS lgc n)
      (by
        simpa [BHW_forwardTube_eq (d := d) (n := n)] using
          bvt_F_holomorphic (d := d) OS lgc n)
      (by
        intro Λ z hz
        exact
          bvt_F_restrictedLorentzInvariant_forwardTube
            (d := d) OS lgc n Λ z
            (by simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz))
      (bvt_F_perm (d := d) OS lgc n)
      hAnchor
      π ρ z hzπ hzρ
```

The new proof-doc target `bvt_F_distributionalJostAnchor_of_OSII` is not a
wrapper.  It is the OS-II content that turns the reconstructed Schwinger
distributions, OS E3 symmetry, and the OS45 local real-edge construction into
the compact-test real-environment data used by Hall-Wightman/EOW.  It must
return adjacent, permutation-indexed real-open patches, scalar-product real
environments, and distributional equality of selected adjacent branch boundary
values there; it must not manufacture a pointwise Schwinger function or a
single real set lying in all permuted sectors.  A theorem named
`BHW.petSectorFiber_adjacent_connected_of_two_le`, if ever proved, is optional
background PET geometry.  It is not an implementation prerequisite for the
strict OS I §4.5 / OS II theorem-2 route unless a later source audit proves
that Hall-Wightman must be decomposed in that particular way.

Lean-ready expansion of the OS-II supplier:

`bvt_F_distributionalJostAnchor_of_OSII` must be built directly from the OS45
local real-edge construction.  It cannot be proved from
`SelectedAdjacentPermutationEdgeData` alone, because that checked selected-edge
record intentionally forgets the Jost membership, the ordered Euclidean
time-sector data, and the scalar-product real-environment information needed by
Hall-Wightman.  The implementation should either enrich the selected-edge
record or introduce the following source-facing OS package next to the
locality files:

```lean
structure SelectedAdjacentDistributionalJostAnchorData
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) where
  basePatch :
    (i : Fin n) -> (hi : i.val + 1 < n) -> Set (NPointDomain d n)
  basePatch_open :
    ∀ i hi, IsOpen (basePatch i hi)
  basePatch_nonempty :
    ∀ i hi, (basePatch i hi).Nonempty
  basePatch_jost :
    ∀ i hi x, x ∈ basePatch i hi -> x ∈ BHW.JostSet d n
  basePatch_left_ET :
    ∀ i hi x, x ∈ basePatch i hi ->
      BHW.realEmbed (d := d) x ∈ BHW.ExtendedTube d n
  basePatch_right_ET :
    ∀ i hi x, x ∈ basePatch i hi ->
      BHW.realEmbed (d := d)
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHW.ExtendedTube d n
  baseGramEnvironment :
    (i : Fin n) -> (hi : i.val + 1 < n) ->
      Set (Fin n -> Fin n -> ℝ)
  baseGramEnvironment_unique :
    ∀ i hi,
      BHW.sourceDistributionalUniquenessSetOnVariety d n
        (baseGramEnvironment i hi)
  baseGram_left_mem :
    ∀ i hi x, x ∈ basePatch i hi ->
      sourceRealMinkowskiGram d n x ∈ baseGramEnvironment i hi
  baseGram_realized :
    ∀ i hi G, G ∈ baseGramEnvironment i hi ->
      ∃ x ∈ basePatch i hi,
        sourceRealMinkowskiGram d n x = G
  baseCompactEq :
    ∀ i hi (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n -> ℂ) ->
      tsupport (φ : NPointDomain d n -> ℂ) ⊆ basePatch i hi ->
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (d := d) x) * φ x
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (d := d)
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
```

Construction of this package is genuine theorem-2 mathematics:

1. obtain `V`, `rho`, all real-edge side conditions, and the single-chart
   branch-difference envelope from the strengthened
   `BHW.os45_adjacent_singleChart_commonBoundaryValue`; its proof in turn
   starts from `BHW.os45_adjacent_localEOWGeometry (d := d) hd i hi`;
2. apply
   `BHW.bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`
   to get the compact-test equality on `V`, using `.symm` if the checked
   theorem is stated in the swap-first orientation;
3. use the checked Hall-Wightman scalar-product geometry lemma
   `BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch` to construct
   `baseGramEnvironment`, its variety-level uniqueness proof, and the
   realization/lift facts.

The Lean implementation target is the following constructor, followed by the
already checked reindexing bridge.  The constructor is the next genuine
mathematical step: it chooses one OS45 patch per adjacent transposition,
proves the Hall-Wightman real-environment property for the Gram image of that
same patch, and obtains compact-test equality from the OS45 EOW envelope.

```lean
noncomputable def bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SelectedAdjacentDistributionalJostAnchorData OS lgc n := by
  classical
  let τ := fun (i : Fin n) (hi : i.val + 1 < n) =>
    Equiv.swap i ⟨i.val + 1, hi⟩

  have hOS45 :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∃ (V : Set (NPointDomain d n)) (rho : Equiv.Perm (Fin n)),
          IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
          (∀ x ∈ V, x ∈ BHW.JostSet d n) ∧
          (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
          (∀ x ∈ V,
            BHW.realEmbed (fun k => x (τ i hi k)) ∈
              BHW.ExtendedTube d n) ∧
          BHW.AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
            (τ i hi) V := by
    intro i hi
    simpa [τ] using
      BHW.os45_adjacent_singleChart_commonBoundaryValue
        (d := d) hd OS lgc n i hi

  choose V rho hV using hOS45

  have hGram :
      ∀ (i : Fin n) (hi : i.val + 1 < n),
        ∃ E : Set (Fin n -> Fin n -> ℝ),
          BHW.sourceDistributionalUniquenessSetOnVariety d n E ∧
          (∀ x ∈ V i hi,
            BHW.sourceRealMinkowskiGram d n x ∈ E) ∧
          (∀ G ∈ E, ∃ x ∈ V i hi,
            BHW.sourceRealMinkowskiGram d n x = G) := by
    intro i hi
    exact
      BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch
        (d := d) n (V i hi)
        (hV i hi).1
        (hV i hi).2.2.1
        (hV i hi).2.2.2.1

  choose E hE using hGram

  refine
    { basePatch := V
      basePatch_open := ?basePatch_open
      basePatch_nonempty := ?basePatch_nonempty
      basePatch_jost := ?basePatch_jost
      basePatch_left_ET := ?basePatch_left_ET
      basePatch_right_ET := ?basePatch_right_ET
      baseGramEnvironment := E
      baseGramEnvironment_unique := ?baseGramEnvironment_unique
      baseGram_left_mem := ?baseGram_left_mem
      baseGram_realized := ?baseGram_realized
      baseCompactEq := ?baseCompactEq }
  · intro i hi
    exact (hV i hi).1
  · intro i hi
    exact (hV i hi).2.2.1
  · intro i hi x hx
    exact (hV i hi).2.2.2.1 x hx
  · intro i hi x hx
    exact (hV i hi).2.2.2.2.1 x hx
  · intro i hi x hx
    exact (hV i hi).2.2.2.2.2.1 x hx
  · intro i hi
    exact (hE i hi).1
  · intro i hi x hx
    exact (hE i hi).2.1 x hx
  · intro i hi G hG
    exact (hE i hi).2.2 G hG
  · intro i hi φ hφ_compact hφ_tsupport
    have hswap_first :=
      BHW.bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope
        (d := d) OS lgc n i hi (V i hi)
        (hV i hi).1
        (hV i hi).2.2.1
        (hV i hi).2.2.2.2.2.2
        φ hφ_compact hφ_tsupport
    simpa [τ] using hswap_first.symm

noncomputable def bvt_F_distributionalJostAnchor_of_OSII
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    BHW.SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) :=
bvt_F_distributionalJostAnchor_of_selectedJostData
    (d := d) OS lgc n
    (bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII
      (d := d) hd OS lgc n)
```

The Gram-environment supplier in the constructor is now checked in
`BHWPermutation/SourceDistributionalUniqueness.lean` as
`exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch`.  It takes
the Gram image of the same nonempty open Jost patch `V`, finds a smaller
regular Hall-Wightman real environment inside it using dense regular
configurations and `sourceRealGramMap_realEnvironmentAt_of_regular`, proves
uniqueness there by
`sourceDistributionalUniquenessSetOnVariety_of_realEnvironment`, and enlarges
to the whole Gram image by `sourceDistributionalUniquenessSetOnVariety_mono`.
The remaining unimplemented input in the constructor is therefore the OS45
common-boundary/EOW envelope theorem
`BHW.os45_adjacent_singleChart_commonBoundaryValue`, not the scalar-product
real-environment uniqueness layer.

Projection audit for the packed `hV i hi` proof:

1. `.1` is `IsOpen (V i hi)`.
2. `.2.1` is `IsConnected (V i hi)`; it is exported for the OS45 EOW proof
   but is not a field of `SelectedAdjacentDistributionalJostAnchorData`.
3. `.2.2.1` is `(V i hi).Nonempty`.
4. `.2.2.2.1` is the Jost-set proof.
5. `.2.2.2.2.1` and `.2.2.2.2.2.1` are the left and adjacent-right
   extended-tube membership proofs.
6. `.2.2.2.2.2.2` is the `AdjacentOSEOWDifferenceEnvelope`.

The constructor deliberately does not invoke
`SelectedAdjacentPermutationEdgeData`: that packet forgets the scalar-product
real environment and the Jost/equal-boundary information.  The only
administrative step after this constructor is the already checked
`bvt_F_distributionalJostAnchor_of_selectedJostData` reindexing bridge.

The last lemma is a genuine SCV/Hall-Wightman geometry theorem, not a wrapper:
it says that the Minkowski-Gram image of the chosen open Jost patch supplies a
Hall-Wightman real environment for the corresponding scalar-product
holomorphic representatives.

The source file now has two checked full-matrix sufficient criteria.  Any
nonempty open real set of full Gram-coordinate matrices is a valid
`sourceDistributionalUniquenessSet`, by applying the existing totally-real
identity theorem in product coordinates `Fin n -> Fin n`:

```lean
theorem BHW.sourceDistributionalUniquenessSet_of_isOpen_nonempty
    (d n : ℕ)
    {E : Set (Fin n -> Fin n -> ℝ)}
    (hE_open : IsOpen E)
    (hE_ne : E.Nonempty) :
    BHW.sourceDistributionalUniquenessSet d n E := by
  refine ⟨hE_ne, ?_⟩
  intro U Φ Ψ hU_open hU_conn hE_sub hΦ hΨ h_eq
  have hsub :
      ∀ G ∈ E, SCV.realToComplexProduct G ∈ U := by
    intro G hG
    simpa [BHW.sourceRealGramComplexify, SCV.realToComplexProduct] using
      hE_sub G hG
  have hzero :
      ∀ G ∈ E, (Φ - Ψ) (SCV.realToComplexProduct G) = 0 := by
    intro G hG
    have hG_eq := h_eq G hG
    simpa [BHW.sourceRealGramComplexify, SCV.realToComplexProduct,
      sub_eq_zero] using hG_eq
  have hident :
      ∀ Z ∈ U, (Φ - Ψ) Z = 0 :=
    SCV.identity_theorem_totally_real_product
      (n := n) (p := n)
      hU_open hU_conn (hΦ.sub hΨ) hE_open hE_ne hsub hzero
  intro Z hZ
  exact sub_eq_zero.mp (hident Z hZ)
```

The source file also has the checked containment version:

```lean
theorem BHW.sourceDistributionalUniquenessSet_of_contains_open
    (d n : ℕ)
    {E O : Set (Fin n -> Fin n -> ℝ)}
    (hO_open : IsOpen O)
    (hO_ne : O.Nonempty)
    (hO_sub : O ⊆ E) :
    BHW.sourceDistributionalUniquenessSet d n E := by
  refine ⟨hO_ne.mono hO_sub, ?_⟩
  intro U Φ Ψ hU_open hU_conn hE_sub hΦ hΨ h_eq
  exact
    (BHW.sourceDistributionalUniquenessSet_of_isOpen_nonempty
      (d := d) (n := n) hO_open hO_ne).2
      U Φ Ψ hU_open hU_conn
      (fun G hG => hE_sub G (hO_sub hG))
      hΦ hΨ
      (fun G hG => h_eq G (hO_sub hG))
```

These two lemmas are true, but they are **not** the general OS supplier for
theorem 2.  The attempted next theorem

```lean
theorem BHW.sourceGramImage_contains_open_of_regularJostPatch
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ne : V.Nonempty)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n) :
    ∃ O : Set (Fin n -> Fin n -> ℝ),
      IsOpen O ∧ O.Nonempty ∧
      O ⊆ BHW.sourceRealMinkowskiGram d n '' V
```

is rejected.  It is mathematically false as a general theorem-2 statement:

1. `BHW.sourceRealMinkowskiGram d n x` is symmetric, so its image lies in the
   proper symmetric linear subspace of `Fin n -> Fin n -> ℝ` whenever `2 <= n`.
   This is now recorded in Lean as `BHW.sourceRealMinkowskiGram_symm`.
2. For arity larger than the spacetime vector dimension `d + 1`, the image lies
   in the rank-`<= d + 1` scalar-product variety, so it also has empty interior
   in the full symmetric matrix space.
3. Hall-Wightman explicitly works on the scalar-product variety of symmetric
   matrices.  The local OCR of `hall_wightman_invariant_analytic_functions_1957.pdf`
   says the scalar products label symmetric matrices, that for large arity the
   domain is open on a `4 n - 6` dimensional algebraic variety in four
   spacetime dimensions, and that the spacelike real points form real
   environments on that variety, not full-matrix open subsets.
4. The API-backed Gemini Deep Research check
   `v1_ChYtLURyYWZ4UjFKNy00d19TbWNMUUJnEhYtLURyYWZ4UjFKNy00d19TbWNMUUJn`
   independently confirmed this correction and recommended fixing the
   production predicate before treating the OS supplier as implementation-ready.

Correct replacement: the OS supplier must target a Hall-Wightman
scalar-product-variety real environment.  The proof-doc contract is therefore
the following Lean surface, with `D = d + 1` the spacetime vector dimension:

```lean
/-- Complex scalar-product variety: the Hall-Wightman variety of symmetric
rank-`<= d + 1` Gram matrices, represented without choosing minors as the
range of the complex Minkowski Gram map. -/
def BHW.sourceComplexGramVariety (d n : ℕ) :
    Set (Fin n -> Fin n -> ℂ) :=
  Set.range (BHW.sourceMinkowskiGram d n)

/-- Real scalar-product variety, represented as the range of the real Gram
map. -/
def BHW.sourceRealGramVariety (d n : ℕ) :
    Set (Fin n -> Fin n -> ℝ) :=
  Set.range (BHW.sourceRealMinkowskiGram d n)

theorem BHW.sourceMinkowskiGram_realEmbed
    (d n : ℕ)
    (x : Fin n -> Fin (d + 1) -> ℝ) :
    BHW.sourceMinkowskiGram d n (BHW.realEmbed x) =
      BHW.sourceRealGramComplexify n
        (BHW.sourceRealMinkowskiGram d n x)

theorem BHW.sourceRealGramComplexify_mem_sourceComplexGramVariety
    (d n : ℕ)
    {G : Fin n -> Fin n -> ℝ}
    (hG : G ∈ BHW.sourceRealGramVariety d n) :
    BHW.sourceRealGramComplexify n G ∈
      BHW.sourceComplexGramVariety d n

def BHW.IsRelOpenInSourceComplexGramVariety
    (d n : ℕ) (U : Set (Fin n -> Fin n -> ℂ)) : Prop :=
  ∃ U0 : Set (Fin n -> Fin n -> ℂ),
    IsOpen U0 ∧ U = U0 ∩ BHW.sourceComplexGramVariety d n

def BHW.IsRelOpenInSourceRealGramVariety
    (d n : ℕ) (E : Set (Fin n -> Fin n -> ℝ)) : Prop :=
  ∃ E0 : Set (Fin n -> Fin n -> ℝ),
    IsOpen E0 ∧ E = E0 ∩ BHW.sourceRealGramVariety d n

def BHW.SourceVarietyHolomorphicOn
    (d n : ℕ)
    (Φ : (Fin n -> Fin n -> ℂ) -> ℂ)
    (U : Set (Fin n -> Fin n -> ℂ)) : Prop :=
  ∀ Z ∈ U, ∃ U0 : Set (Fin n -> Fin n -> ℂ),
    IsOpen U0 ∧ Z ∈ U0 ∧
      DifferentiableOn ℂ Φ U0 ∧
      U0 ∩ BHW.sourceComplexGramVariety d n ⊆ U

def BHW.sourceDistributionalUniquenessSetOnVariety
    (d n : ℕ)
    (E : Set (Fin n -> Fin n -> ℝ)) : Prop :=
  E.Nonempty ∧
    ∀ (U : Set (Fin n -> Fin n -> ℂ))
      (Φ Ψ : (Fin n -> Fin n -> ℂ) -> ℂ),
      BHW.IsRelOpenInSourceComplexGramVariety d n U ->
      IsConnected U ->
      (∀ G ∈ E,
        BHW.sourceRealGramComplexify n G ∈ U) ->
      BHW.SourceVarietyHolomorphicOn d n Φ U ->
      BHW.SourceVarietyHolomorphicOn d n Ψ U ->
      (∀ G ∈ E,
        Φ (BHW.sourceRealGramComplexify n G) =
          Ψ (BHW.sourceRealGramComplexify n G)) ->
      Set.EqOn Φ Ψ U
```

The production anchor now carries
`BHW.sourceDistributionalUniquenessSetOnVariety`; the older
`BHW.sourceDistributionalUniquenessSet` remains only as a full-matrix
sufficient predicate.  The checked full-matrix lemmas may remain as
small-arity/full-dimensional sufficient tools, but they must not be used to
claim that a general OS45 Jost patch has full matrix interior.

The checked OS-side Gram-environment supplier is:

```lean
theorem BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch
    [NeZero d]
    (n : ℕ)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ne : V.Nonempty)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n) :
    ∃ E : Set (Fin n -> Fin n -> ℝ),
      BHW.sourceDistributionalUniquenessSetOnVariety d n E ∧
      (∀ x ∈ V, BHW.sourceRealMinkowskiGram d n x ∈ E) ∧
      (∀ G ∈ E, ∃ x ∈ V,
        BHW.sourceRealMinkowskiGram d n x = G)
```

This theorem is now checked in
`BHWPermutation/SourceDistributionalUniqueness.lean`.  It is the genuine
Hall-Wightman geometry step packaged for the selected OS45 real-open Jost slice:
the whole Gram image is a variety-level uniqueness environment because it
contains a smaller regular Hall-Wightman real environment.  It is **not** a
claim about full-matrix interior.

Checked decomposition of this geometry step:

```lean
/-- Dimension of the regular Hall-Wightman scalar-product variety.
For `D = d + 1` and `m = min n D`, this is
`n * m - m * (m - 1) / 2`; in four spacetime dimensions this gives
`1, 3, 6, 10, 4n - 6`, matching Hall-Wightman. -/
def BHW.sourceGramExpectedDim (d n : ℕ) : ℕ :=
  let m := min n (d + 1)
  n * m - (m * (m - 1)) / 2

/-- The span of the source vectors in real spacetime. -/
def BHW.sourceConfigurationSpan
    (d n : ℕ)
    (x : NPointDomain d n) :
    Submodule ℝ (Fin (d + 1) -> ℝ) :=
  Submodule.span ℝ (Set.range x)

/-- Regular real configurations are the maximal-span configurations.  For the
nondegenerate Minkowski form this is exactly the regular stratum of the Gram
map onto the Hall-Wightman scalar-product variety. -/
def BHW.SourceGramRegularAt
    (d n : ℕ)
    (x : NPointDomain d n) : Prop :=
  Module.finrank ℝ (BHW.sourceConfigurationSpan d n x) =
    min n (d + 1)

/-- Differential of the real source Gram map at `x`. -/
def BHW.sourceRealGramDifferential
    (d n : ℕ)
    (x : NPointDomain d n) :
    NPointDomain d n →ₗ[ℝ] (Fin n -> Fin n -> ℝ) :=
{ toFun := fun h i j =>
    ∑ μ : Fin (d + 1),
      MinkowskiSpace.metricSignature d μ *
        (h i μ * x j μ + x i μ * h j μ)
  map_add' := by
    intro h₁ h₂
    ext i j
    simp [add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c h
    ext i j
    simp [mul_add, Finset.mul_sum]
    ring }

/-- Regular configurations have the expected differential rank. -/
theorem BHW.sourceRealGramDifferential_rank_of_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    Module.finrank ℝ
      (LinearMap.range (BHW.sourceRealGramDifferential d n x)) =
      BHW.sourceGramExpectedDim d n

/-- Complex span of source vectors. -/
def BHW.sourceComplexConfigurationSpan
    (d n : ℕ)
    (z : Fin n -> Fin (d + 1) -> ℂ) :
    Submodule ℂ (Fin (d + 1) -> ℂ) :=
  Submodule.span ℂ (Set.range z)

/-- Regular complex configurations are the maximal complex-span
configurations. -/
def BHW.SourceComplexGramRegularAt
    (d n : ℕ)
    (z : Fin n -> Fin (d + 1) -> ℂ) : Prop :=
  Module.finrank ℂ (BHW.sourceComplexConfigurationSpan d n z) =
    min n (d + 1)

/-- Differential of the complex source Gram map. -/
def BHW.sourceComplexGramDifferential
    (d n : ℕ)
    (z : Fin n -> Fin (d + 1) -> ℂ) :
    (Fin n -> Fin (d + 1) -> ℂ) →ₗ[ℂ] (Fin n -> Fin n -> ℂ) :=
{ toFun := fun h i j =>
    ∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) *
        (h i μ * z j μ + z i μ * h j μ)
  map_add' := by
    intro h₁ h₂
    ext i j
    simp [add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c h
    ext i j
    simp [mul_add, Finset.mul_sum]
    ring }

/-- Maximal-rank configurations are dense in real configuration space. -/
theorem BHW.dense_sourceGramRegularAt
    (d n : ℕ) :
    Dense {x : NPointDomain d n | BHW.SourceGramRegularAt d n x}

/-- The regular locus is open. -/
theorem BHW.isOpen_sourceGramRegularAt
    (d n : ℕ) :
    IsOpen {x : NPointDomain d n | BHW.SourceGramRegularAt d n x}

/-- Real tangent space supplied by the Gram differential at a regular
representative. -/
def BHW.sourceRealGramTangentSpaceAt
    (d n : ℕ)
    (G : Fin n -> Fin n -> ℝ) :
    Set (Fin n -> Fin n -> ℝ) :=
  {δG | ∃ x : NPointDomain d n,
    BHW.SourceGramRegularAt d n x ∧
    BHW.sourceRealMinkowskiGram d n x = G ∧
    δG ∈ LinearMap.range (BHW.sourceRealGramDifferential d n x)}

/-- Complex tangent space supplied by the complex Gram differential at a
regular representative. -/
def BHW.sourceComplexGramTangentSpaceAt
    (d n : ℕ)
    (Z : Fin n -> Fin n -> ℂ) :
    Set (Fin n -> Fin n -> ℂ) :=
  {δZ | ∃ z : Fin n -> Fin (d + 1) -> ℂ,
    BHW.SourceComplexGramRegularAt d n z ∧
    BHW.sourceMinkowskiGram d n z = Z ∧
    δZ ∈ LinearMap.range (BHW.sourceComplexGramDifferential d n z)}

/-- The Hall-Wightman real locus is maximal totally real at `G`: after
complexification, the real tangent supplied by the regular real Gram map has
complex span equal to the complex tangent of the scalar-product variety. -/
def BHW.SourceComplexifiedRealTangentEqualsComplexTangent
    (d n : ℕ)
    (G : Fin n -> Fin n -> ℝ) : Prop :=
  Submodule.span ℂ
      (BHW.sourceRealGramComplexify n ''
        BHW.sourceRealGramTangentSpaceAt d n G) =
    Submodule.span ℂ
      (BHW.sourceComplexGramTangentSpaceAt d n
        (BHW.sourceRealGramComplexify n G))

-- The proof chooses a regular point in `V` by
-- `(BHW.dense_sourceGramRegularAt d n).exists_mem_open hV_open hV_ne`.

/-- Hall-Wightman's real-environment predicate.  `O` contains a relatively open
regular real Gram patch, realized by Jost configurations, whose complexified
real tangent space is the complex tangent space of the scalar-product variety.
This is the Bochner-Martin/Hall-Wightman "real environment" condition, not a
full-matrix openness condition. -/
structure BHW.IsHWRealEnvironment
    (d n : ℕ)
    (O : Set (Fin n -> Fin n -> ℝ)) : Prop where
  nonempty : O.Nonempty
  relOpen : BHW.IsRelOpenInSourceRealGramVariety d n O
  realized_by_jost :
    ∀ G ∈ O, ∃ x : NPointDomain d n,
      x ∈ BHW.JostSet d n ∧
      BHW.SourceGramRegularAt d n x ∧
      BHW.sourceRealMinkowskiGram d n x = G
  maximal_totally_real :
    ∀ G ∈ O,
      BHW.SourceComplexifiedRealTangentEqualsComplexTangent d n G

/-- At a regular real Jost configuration, the real Gram map is relatively open
onto a Hall-Wightman real environment in the scalar-product variety. -/
theorem BHW.sourceRealGramMap_realEnvironmentAt_of_regular
    [NeZero d]
    (n : ℕ)
    {x0 : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x0)
    (hx0_jost : x0 ∈ BHW.JostSet d n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hx0V : x0 ∈ V) :
    ∃ O : Set (Fin n -> Fin n -> ℝ),
      O ⊆ BHW.sourceRealMinkowskiGram d n '' V ∧
      BHW.IsHWRealEnvironment d n O

/-- Hall-Wightman's real-environment uniqueness theorem on the scalar-product
variety.  This is the source-backed analytic theorem, not a wrapper around the
full-matrix totally-real identity theorem. -/
theorem BHW.sourceDistributionalUniquenessSetOnVariety_of_realEnvironment
    [NeZero d]
    (n : ℕ)
    {E : Set (Fin n -> Fin n -> ℝ)}
    (hE_env : BHW.IsHWRealEnvironment d n E) :
    BHW.sourceDistributionalUniquenessSetOnVariety d n E

/-- Variety-level uniqueness is monotone in the real environment.  This checked
Lean lemma lets the OS supplier use the whole Gram image of the selected patch
after proving that it contains a smaller Hall-Wightman real environment. -/
theorem BHW.sourceDistributionalUniquenessSetOnVariety_mono
    (d n : ℕ)
    {O E : Set (Fin n -> Fin n -> ℝ)}
    (hO : BHW.sourceDistributionalUniquenessSetOnVariety d n O)
    (hOE : O ⊆ E) :
    BHW.sourceDistributionalUniquenessSetOnVariety d n E
```

The checked proof of
`BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch` is:

```lean
  classical
  let E : Set (Fin n -> Fin n -> ℝ) :=
    BHW.sourceRealMinkowskiGram d n '' V
  obtain ⟨x0, hreg, hx0V⟩ :=
    (BHW.dense_sourceGramRegularAt d n).exists_mem_open hV_open hV_ne
  have hx0_jost : x0 ∈ BHW.JostSet d n := hV_jost x0 hx0V
  obtain ⟨O, hO_sub_E, hO_env⟩ :=
    BHW.sourceRealGramMap_realEnvironmentAt_of_regular
      (d := d) (n := n) hreg hx0_jost V hV_open hx0V
  have hO_unique :
      BHW.sourceDistributionalUniquenessSetOnVariety d n O :=
    BHW.sourceDistributionalUniquenessSetOnVariety_of_realEnvironment
      (d := d) (n := n) hO_env
  have hE_unique :
      BHW.sourceDistributionalUniquenessSetOnVariety d n E :=
    BHW.sourceDistributionalUniquenessSetOnVariety_mono
      (d := d) (n := n) hO_unique hO_sub_E
  refine ⟨E, hE_unique, ?_, ?_⟩
  · intro x hxV
    exact ⟨x, hxV, rfl⟩
  · intro G hG
    rcases hG with ⟨x, hxV, rfl⟩
    exact ⟨x, hxV, rfl⟩
```

The implementation keeps the source-level `IsHWRealEnvironment` theorem and
the uniqueness theorem separate, then packages their consequence for open Jost
patches in `SourceDistributionalUniqueness.lean`.  It must not be replaced by
an assertion of openness in `Fin n -> Fin n -> ℝ`.

Detailed proof obligations for the remaining supplier facts:

Current next-stage gate after the `SourceExtension.lean` cleanup:

1. Do not add a new production theorem for
   `exists_sourceAdjacentOverlapWitness_of_mem_doubleDomain` or any synonym of
   it.  That theorem is source-equivalent and remains proof-doc-only.
2. The next production theorem on the OS side is the constructor
   `bvt_F_selectedAdjacentDistributionalJostAnchorData_of_OSII`; it is allowed
   only after its remaining mathematical suppliers are either checked or
   recorded as exact theorem-level source frontiers:
   - `BHW.os45_adjacent_singleChart_commonBoundaryValue`, supplying one OS45
     patch `V` with Jost membership, left/right adjacent ET membership, and an
     `AdjacentOSEOWDifferenceEnvelope`;
   - `BHW.exists_sourceDistributionalUniquenessEnvironment_of_open_jost_patch`,
     already checked, supplying the scalar-product real environment/uniqueness
     package for the Gram image of that same `V`;
   - `BHW.bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`,
     already checked, converting the OS45 envelope into the compact-test
     equality field.
3. The next production theorem on the BHW source side is not another local
   overlap lemma.  It is the direct source theorem
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
   with `hallWightman_exists_sourceScalarRepresentative_of_forwardTube_lorentz`
   as the ordinary scalar-representative source input.
4. The real-environment geometry has been implemented in the small companion
   module `BHWPermutation/SourceDistributionalUniqueness.lean`, exported by the
   `BHWPermutation` aggregate.  It contains only finite-dimensional Gram-map and
   Hall-Wightman real-environment facts and does not mention OS, Schwinger
   functions, locality, or `bvt_F`.
5. Checked algebraic support now in
   `BHWPermutation/SourceExtension.lean`:
   `sourceRealGramDifferential`, `sourceComplexGramDifferential`,
   `sourceRealMinkowskiGram_hasFDerivAt`,
   `sourceComplexGramDifferential_realEmbed`,
   `sourceRealGramTangentSpaceAt`, `sourceComplexGramTangentSpaceAt`,
   `SourceComplexifiedRealTangentEqualsComplexTangent`, and
   `IsHWRealEnvironment`.  The regular-locus template support is also checked:
   `sourceTemplateDomainIndex`, `sourceTemplateCoordIndex`,
   `sourceTemplateDomainIndex_injective`,
   `sourceTemplateCoordIndex_injective`,
   `sourceFullSpanTemplate_basisVector`,
   `linearIndependent_sourceFullSpanTemplate_basisBlock`,
   `sourceFullSpanTemplate_regular`, `sourceRegularMinor`,
   `continuous_sourceRegularMinor`,
   `exists_nonzero_coordinate_minor_of_linearIndependent`,
   `sourceGramRegularAt_of_exists_nonzero_minor`,
   `exists_nonzero_minor_of_sourceGramRegularAt`, and
   `sourceGramRegularAt_iff_exists_nonzero_minor`,
   `isOpen_sourceGramRegularAt`,
   `sourceFullSpanTemplate_regularMinor_eq_one`, and
   `sourceFullSpanTemplate_regularMinor_ne_zero`, together with the
   determinant-line polynomial facts
   `sourceCanonicalRegularMinorLinePolynomial`,
   `sourceCanonicalRegularMinorLinePolynomial_leadingCoeff`,
   `sourceCanonicalRegularMinorLinePolynomial_ne_zero`,
   `sourceCanonicalRegularMinorLinePolynomial_eval`,
   `sourceCanonicalRegularMinor_nonzero_dense`, and
   `dense_sourceGramRegularAt`.  Post-cleanup rank-stage support now starts in
   `BHWPermutation/SourceRegularRank.lean`; the smoothness theorem
   `contDiff_sourceRealMinkowskiGram`, the selected-coordinate projection
   `sourceSelectedGramCoord`, the symmetric selected-coordinate target
   `sourceSelectedSymCoordSubspace`,
   `linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero`,
   `span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero`,
   `sourceSelectedGramCoord_differential_mem`,
   `minkowskiInner_dualVectorOfLinearFunctional`,
   `exists_minkowski_dual_family_of_linearIndependent`, and
   `exists_minkowski_dual_sourceRows_of_sourceRegularMinor_ne_zero`,
   plus the projected-range theorem
   `sourceSelectedGramCoord_comp_differential_range_eq`, are checked there.
   These are
   definitions, finite-dimensional linear algebra, determinant-polynomial root
   avoidance, and finite-union topological arguments only; they do not assert
   the Gram-map
   differential-rank theorem,
   constant-rank local charts, Hall-Wightman uniqueness, or the global
   `S''_n` source branch theorem.

**A. Dense/open regular configurations.**

The Lean proof of `dense_sourceGramRegularAt` and
`isOpen_sourceGramRegularAt` should use ordinary finite-dimensional linear
algebra, not Hall-Wightman.

Implementation order for the regular-locus package:

1. introduce the two inclusion maps for the template basis block; checked in
   `SourceExtension.lean`;
2. prove the corresponding template vectors are ordinary coordinate basis
   vectors; checked in `SourceExtension.lean`;
3. prove the maximal-span template is regular; checked in
   `SourceExtension.lean`;
4. define maximal coordinate minors and prove their continuity; checked in
   `SourceExtension.lean`;
5. characterize regularity by one nonzero maximal minor; checked in
   `SourceExtension.lean`;
6. prove openness from the nonzero-minor characterization; checked in
   `SourceExtension.lean`;
7. prove the canonical template minor is `1` and hence nonzero; checked in
   `SourceExtension.lean`;
8. prove density by perturbing along the regular template and avoiding the
   finite zero set of the nonzero determinant polynomial
   `det(t I + B)`; checked in `SourceExtension.lean`.

Checked Lean surfaces for steps 1-8:

```lean
def BHW.sourceTemplateDomainIndex
    (d n : ℕ) :
    Fin (min n (d + 1)) -> Fin n :=
  fun a => ⟨a.val, lt_of_lt_of_le a.isLt (Nat.min_le_left n (d + 1))⟩

def BHW.sourceTemplateCoordIndex
    (d n : ℕ) :
    Fin (min n (d + 1)) -> Fin (d + 1) :=
  fun a => ⟨a.val, lt_of_lt_of_le a.isLt (Nat.min_le_right n (d + 1))⟩

theorem BHW.sourceTemplateCoordIndex_injective
    (d n : ℕ) :
    Function.Injective (BHW.sourceTemplateCoordIndex d n)

theorem BHW.sourceTemplateDomainIndex_injective
    (d n : ℕ) :
    Function.Injective (BHW.sourceTemplateDomainIndex d n)

theorem BHW.sourceFullSpanTemplate_basisVector
    (d n : ℕ)
    (a : Fin (min n (d + 1))) :
    BHW.sourceFullSpanTemplate d n
        (BHW.sourceTemplateDomainIndex d n a) =
      Pi.single (M := fun _ : Fin (d + 1) => ℝ)
        (BHW.sourceTemplateCoordIndex d n a) (1 : ℝ)

theorem BHW.linearIndependent_sourceFullSpanTemplate_basisBlock
    (d n : ℕ) :
    LinearIndependent ℝ
      (fun a : Fin (min n (d + 1)) =>
        BHW.sourceFullSpanTemplate d n
          (BHW.sourceTemplateDomainIndex d n a))

theorem BHW.sourceFullSpanTemplate_regular
    (d n : ℕ) :
    BHW.SourceGramRegularAt d n (BHW.sourceFullSpanTemplate d n)

def BHW.sourceRegularMinor
    (d n : ℕ)
    (I : Fin (min n (d + 1)) -> Fin n)
    (J : Fin (min n (d + 1)) -> Fin (d + 1))
    (x : NPointDomain d n) : ℝ :=
  Matrix.det (fun a b => x (I a) (J b))

theorem BHW.continuous_sourceRegularMinor
    (d n : ℕ)
    (I : Fin (min n (d + 1)) -> Fin n)
    (J : Fin (min n (d + 1)) -> Fin (d + 1)) :
    Continuous (BHW.sourceRegularMinor d n I J)

theorem BHW.exists_nonzero_coordinate_minor_of_linearIndependent
    {m D : ℕ}
    {v : Fin m -> Fin D -> ℝ}
    (hli : LinearIndependent ℝ v) :
    ∃ J : Fin m -> Fin D,
      Function.Injective J ∧
      Matrix.det (fun a b => v a (J b)) ≠ 0

theorem BHW.sourceGramRegularAt_of_exists_nonzero_minor
    (d n : ℕ)
    {x : NPointDomain d n}
    (hminor :
      ∃ I : Fin (min n (d + 1)) -> Fin n,
        Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) -> Fin (d + 1),
          Function.Injective J ∧
          BHW.sourceRegularMinor d n I J x ≠ 0) :
    BHW.SourceGramRegularAt d n x

theorem BHW.exists_nonzero_minor_of_sourceGramRegularAt
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    ∃ I : Fin (min n (d + 1)) -> Fin n,
      Function.Injective I ∧
      ∃ J : Fin (min n (d + 1)) -> Fin (d + 1),
        Function.Injective J ∧
        BHW.sourceRegularMinor d n I J x ≠ 0

theorem BHW.sourceGramRegularAt_iff_exists_nonzero_minor
    (d n : ℕ)
    (x : NPointDomain d n) :
    BHW.SourceGramRegularAt d n x ↔
      ∃ I : Fin (min n (d + 1)) -> Fin n,
        Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) -> Fin (d + 1),
          Function.Injective J ∧
          BHW.sourceRegularMinor d n I J x ≠ 0

theorem BHW.isOpen_sourceGramRegularAt
    (d n : ℕ) :
    IsOpen {x : NPointDomain d n | BHW.SourceGramRegularAt d n x}

theorem BHW.sourceFullSpanTemplate_regularMinor_eq_one
    (d n : ℕ) :
    BHW.sourceRegularMinor d n
        (BHW.sourceTemplateDomainIndex d n)
        (BHW.sourceTemplateCoordIndex d n)
        (BHW.sourceFullSpanTemplate d n) = 1

theorem BHW.sourceFullSpanTemplate_regularMinor_ne_zero
    (d n : ℕ) :
    BHW.sourceRegularMinor d n
        (BHW.sourceTemplateDomainIndex d n)
        (BHW.sourceTemplateCoordIndex d n)
        (BHW.sourceFullSpanTemplate d n) ≠ 0

def BHW.sourceCanonicalRegularMinorLinePolynomial
    (d n : ℕ)
    (x : NPointDomain d n) : Polynomial ℝ :=
  Matrix.det ((Polynomial.X : Polynomial ℝ) •
      (1 : Matrix (Fin (min n (d + 1)))
        (Fin (min n (d + 1))) (Polynomial ℝ)) +
    (fun a b : Fin (min n (d + 1)) =>
      Polynomial.C
        (x (BHW.sourceTemplateDomainIndex d n a)
          (BHW.sourceTemplateCoordIndex d n b))))

theorem BHW.sourceCanonicalRegularMinorLinePolynomial_leadingCoeff
    (d n : ℕ)
    (x : NPointDomain d n) :
    Polynomial.leadingCoeff
      (BHW.sourceCanonicalRegularMinorLinePolynomial d n x) = 1

theorem BHW.sourceCanonicalRegularMinorLinePolynomial_ne_zero
    (d n : ℕ)
    (x : NPointDomain d n) :
    BHW.sourceCanonicalRegularMinorLinePolynomial d n x ≠ 0

theorem BHW.sourceCanonicalRegularMinorLinePolynomial_eval
    (d n : ℕ)
    (x : NPointDomain d n)
    (t : ℝ) :
    (BHW.sourceCanonicalRegularMinorLinePolynomial d n x).eval t =
      BHW.sourceRegularMinor d n
        (BHW.sourceTemplateDomainIndex d n)
        (BHW.sourceTemplateCoordIndex d n)
        (x + t • BHW.sourceFullSpanTemplate d n)

theorem BHW.sourceCanonicalRegularMinor_nonzero_dense
    (d n : ℕ) :
    Dense {x : NPointDomain d n |
      BHW.sourceRegularMinor d n
        (BHW.sourceTemplateDomainIndex d n)
        (BHW.sourceTemplateCoordIndex d n) x ≠ 0}

theorem BHW.dense_sourceGramRegularAt
    (d n : ℕ) :
    Dense {x : NPointDomain d n | BHW.SourceGramRegularAt d n x}
```

Proof transcript for `sourceFullSpanTemplate_regular`:

1. Let `m := min n (d + 1)`.
2. Use `sourceFullSpanTemplate_basisVector` to identify the selected template
   vectors with the first `m` coordinate vectors.
3. Use `(Pi.basisFun ℝ (Fin (d + 1))).linearIndependent`, composed with
   `sourceTemplateCoordIndex` and `sourceTemplateCoordIndex_injective`, to get
   linear independence of the selected coordinate vectors.
4. Map that linear independence across the equality from step 2 to prove
   `linearIndependent_sourceFullSpanTemplate_basisBlock`.
5. Each selected template vector lies in
   `sourceConfigurationSpan d n (sourceFullSpanTemplate d n)` by
   `Submodule.subset_span` applied to the corresponding element of
   `Set.range`.
6. Therefore the span has finrank at least `m`.
7. It has finrank at most `m` by combining
   `finrank_range_le_card (b := sourceFullSpanTemplate d n)` with
   `Submodule.finrank_le` and `Module.finrank_fin_fun`, giving upper bounds
   `n` and `d + 1`, hence the `min`.
8. Combine the two inequalities with antisymmetry and unfold
   `SourceGramRegularAt`.

Proof transcript for `sourceGramRegularAt_of_exists_nonzero_minor`:

1. unpack `I`, `J`, and the nonzero determinant of the selected square minor;
2. define the coordinate-restriction linear map
   `restrictJ : (Fin (d + 1) -> ℝ) ->ₗ[ℝ]
     (Fin (min n (d + 1)) -> ℝ)` by `(restrictJ v) b = v (J b)`;
3. use `Matrix.linearIndependent_rows_of_det_ne_zero` on the minor matrix to
   obtain linear independence of
   `fun a b => x (I a) (J b)`;
4. apply `LinearIndependent.of_comp restrictJ` to lift this to linear
   independence of `fun a => x (I a)` in the full coordinate space;
5. coerce these selected rows into
   `sourceConfigurationSpan d n x` using `Submodule.subset_span ⟨I a, rfl⟩`;
6. `fintype_card_le_finrank` gives the lower bound
   `min n (d + 1) <= Module.finrank ℝ (sourceConfigurationSpan d n x)`;
7. `finrank_range_le_card (b := x)`, `Submodule.finrank_le`, and
   `Module.finrank_fin_fun` give the upper bound by the same `min`;
8. use `le_antisymm` and unfold `SourceGramRegularAt`.

Proof transcript for `exists_nonzero_coordinate_minor_of_linearIndependent`:

1. set `A : Matrix (Fin m) (Fin D) ℝ := fun a j => v a j`;
2. from `hli`, get
   `Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) = m` using
   `finrank_span_eq_card`;
3. use `Matrix.rank_eq_finrank_span_row` and
   `Matrix.rank_eq_finrank_span_cols` to conclude the column span of `A` also
   has finrank `m`;
4. apply `Submodule.exists_fun_fin_finrank_span_eq` to `Set.range A.col` and
   reindex by `finCongr hcolrank.symm` to choose `m` independent columns from
   actual columns of `A`;
5. define `J` by choosing each column preimage and prove `J` injective from
   `LinearIndependent.injective`;
6. the selected square matrix has linearly independent columns, so
   `Matrix.linearIndependent_cols_iff_isUnit` and
   `B.isUnit_iff_isUnit_det` give nonzero determinant.

Proof transcript for `exists_nonzero_minor_of_sourceGramRegularAt`:

1. rewrite `hreg` as
   `Module.finrank ℝ (Submodule.span ℝ (Set.range x)) = min n (d + 1)`;
2. use `Submodule.exists_fun_fin_finrank_span_eq` on `Set.range x` and
   reindex by that equality to obtain a linearly independent selected row
   family of size `min n (d + 1)`;
3. choose row preimages `I a : Fin n`, prove the selected rows are still
   linearly independent, and prove `I` injective from
   `LinearIndependent.injective`;
4. apply `exists_nonzero_coordinate_minor_of_linearIndependent` to the
   selected rows and package the resulting `J` and nonzero determinant.

Proof transcript for `isOpen_sourceGramRegularAt`:

1. rewrite the regular locus by
   `sourceGramRegularAt_iff_exists_nonzero_minor`;
2. identify it with the finite union over row maps `I`, proofs of
   `Function.Injective I`, column maps `J`, and proofs of
   `Function.Injective J` of the sets
   `{x | sourceRegularMinor d n I J x ≠ 0}`;
3. each such set is open by `isOpen_ne_fun
   (continuous_sourceRegularMinor d n I J) continuous_const`;
4. close with repeated `isOpen_iUnion`.

Proof transcript for `sourceFullSpanTemplate_regularMinor_eq_one`:

1. unfold `sourceRegularMinor`;
2. use `sourceFullSpanTemplate_basisVector` to rewrite the canonical minor
   matrix as the identity matrix on `Fin (min n (d + 1))`;
3. use `sourceTemplateCoordIndex_injective` to identify equality of selected
   coordinate indices with equality of row/column indices;
4. conclude the determinant is `1`; the nonzero theorem is `rw` plus
   `norm_num`.

Proof transcript for `sourceCanonicalRegularMinorLinePolynomial_eval` and
`sourceCanonicalRegularMinor_nonzero_dense`:

1. For fixed `x`, set `I0 := sourceTemplateDomainIndex d n`,
   `J0 := sourceTemplateCoordIndex d n`, and
   `B a b := x (I0 a) (J0 b)`.
2. Define the line-minor polynomial
   `p_x(t) := det(t I + B)` as
   `sourceCanonicalRegularMinorLinePolynomial d n x`.
3. Mathlib's
   `Polynomial.leadingCoeff_det_X_one_add_C` gives
   `leadingCoeff p_x = 1`, hence `p_x ≠ 0`.
4. The evaluation identity is checked by expanding both determinants with
   `Matrix.det_apply'` and `Polynomial.eval_finset_sum`: for every `t`,
   `p_x.eval t` is the canonical minor of
   `x + t • sourceFullSpanTemplate d n`.  The entrywise step uses
   `sourceFullSpanTemplate_basisVector` and
   `sourceTemplateCoordIndex_injective` to identify the selected template
   block with the identity matrix.
5. For an arbitrary nonempty open set `U`, choose `x ∈ U` and consider
   `line t := x + t • sourceFullSpanTemplate d n`.
6. The root set `{t | p_x.eval t = 0}` is finite because it is contained in
   `p_x.roots.toFinset`.
7. `Dense.diff_finite dense_univ` gives density of the complement of that
   finite root set in `ℝ`.
8. The preimage `line ⁻¹' U` is open and contains `0`, so the dense complement
   supplies `t` with `line t ∈ U` and `p_x.eval t ≠ 0`.
9. By the evaluation identity, `line t` lies in the canonical nonzero-minor
   locus; hence that locus is dense.
10. Since the canonical row and column selections are injective, the checked
    theorem `sourceGramRegularAt_of_exists_nonzero_minor` maps the dense
    canonical nonzero-minor locus into the full regular locus, proving
    `dense_sourceGramRegularAt`.

**B. Differential rank and local real environments.**

At a regular configuration, the derivative

```lean
dG_x(h) i j =
  ∑ μ, η_μ * (h i μ * x j μ + x i μ * h j μ)
```

has rank `sourceGramExpectedDim d n`.  This is the next genuine mathematical
frontier.  The local real-environment theorem must not be written as a
wrapper around an unavailable generic constant-rank theorem: this mathlib
checkout has inverse-function-theorem and local-diffeomorphism infrastructure,
but no ready general constant-rank/submersion API.  The Lean route should
therefore implement the standard proof of the constant-rank chart for this
specific finite-dimensional Gram map.

The rank calculation should be formalized by a selected-coordinate projection,
not by trying to characterize the whole ambient matrix space at once.  This
keeps the Lean target finite and exact.

Let `m = min n (d + 1)` and put `D = d + 1`.  From a nonzero regular minor,
choose

```lean
I : Fin m -> Fin n
J : Fin m -> Fin D
hI : Function.Injective I
hJ : Function.Injective J
hdet : sourceRegularMinor d n I J x ≠ 0
```

Then:

1. `hdet` gives linear independence of the selected source rows
   `e a := x (I a)`.  This is already the same determinant argument used in
   `sourceGramRegularAt_of_exists_nonzero_minor`, but the rank proof should
   expose it as a reusable selected-row lemma.
2. `sourceGramRegularAt_of_exists_nonzero_minor` gives
   `SourceGramRegularAt d n x`, hence the full source span has dimension `m`.
   Since the selected rows are an independent `m`-tuple inside that span, their
   span equals `sourceConfigurationSpan d n x`.
3. For every row `r : Fin n`, choose coefficients
   `c r : Fin m -> ℝ` with
   `x r = ∑ a, c r a • x (I a)`.  In Lean, obtain these coefficients from the
   selected basis of the source span, not by a dummy `Classical.choose` over an
   underspecified equation.
4. Define the selected-column projection on Gram variations:

```lean
def sourceSelectedGramCoord
    (n m : ℕ) (I : Fin m -> Fin n) :
    (Fin n -> Fin n -> ℝ) →ₗ[ℝ] (Fin n -> Fin m -> ℝ) :=
{ toFun := fun δ i a => δ i (I a), ... }
```

5. Define the genuine coordinate target subspace

```lean
def sourceSelectedSymCoordSubspace
    (n m : ℕ) (I : Fin m -> Fin n) :
    Submodule ℝ (Fin n -> Fin m -> ℝ) :=
{ A | ∀ a b : Fin m, A (I a) b = A (I b) a }
```

This subspace records all pairings with the selected rows, with exactly the
symmetry relations on the selected `m × m` block.  Its dimension is

```lean
n * m - (m * (m - 1)) / 2
```

The Lean proof should use a codimension calculation, not an ad hoc complement
construction.  Define the strict-upper selected-pair type and skew-coordinate
map:

```lean
def sourceSelectedUpperPair (m : ℕ) :=
  {p : Fin m × Fin m // p.1 < p.2}

def sourceSelectedSkewCoord
    (n m : ℕ) (I : Fin m -> Fin n) :
    (Fin n -> Fin m -> ℝ) →ₗ[ℝ]
      (sourceSelectedUpperPair m -> ℝ) :=
{ toFun := fun A p => A (I p.1.1) p.1.2 - A (I p.1.2) p.1.1, ... }
```

Then:

```lean
theorem sourceSelectedSkewCoord_ker
    (n m : ℕ) (I : Fin m -> Fin n) :
    LinearMap.ker (sourceSelectedSkewCoord n m I) =
      sourceSelectedSymCoordSubspace n m I
```

The proof is by `lt_trichotomy a b`: the strict-upper equation gives
`A(I a)b = A(I b)a` when `a < b`, the reversed strict-upper equation gives it
when `b < a`, and the diagonal case is reflexive.

For surjectivity, use the injective selected-row index:

```lean
theorem sourceSelectedSkewCoord_surjective
    (n m : ℕ) (I : Fin m -> Fin n)
    (hI : Function.Injective I) :
    Function.Surjective (sourceSelectedSkewCoord n m I)
```

Given `B : sourceSelectedUpperPair m -> ℝ`, set

```lean
A r b :=
  if hr : r ∈ Set.range I then
    let a := (Equiv.ofInjective I hI).symm ⟨r, hr⟩
    if hlt : a < b then B ⟨(a, b), hlt⟩ else 0
  else 0
```

Then for `a < b`, `A(I a)b = B(a,b)` and `A(I b)a = 0`, so the skew map
returns `B`.  This gives range `⊤`.

Count the strict-upper pair type by the equivalence

```lean
sourceSelectedUpperPair m ≃ Sigma (fun b : Fin m => Fin b.val)
```

and hence

```lean
Fintype.card (sourceSelectedUpperPair m)
  = ∑ b : Fin m, b.val
  = m * (m - 1) / 2.
```

Rank-nullity for `sourceSelectedSkewCoord n m I`, together with
`Module.finrank_fintype_fun_eq_card` and `Module.finrank_pi`, gives

```lean
Module.finrank ℝ (sourceSelectedSymCoordSubspace n m I) =
  n * m - m * (m - 1) / 2.
```

6. The projected differential lands in this subspace:

```lean
sourceSelectedGramCoord n m I
  ((sourceRealGramDifferential d n x) h) ∈
sourceSelectedSymCoordSubspace n m I
```

The proof is just symmetry of the differential:
`dG_x(h) (I a) (I b) = dG_x(h) (I b) (I a)`.

7. The projected differential is surjective onto this subspace.  Let
`A : Fin n -> Fin m -> ℝ` satisfy the selected-block symmetry.  Since the
Minkowski form is nondegenerate and the selected rows are independent, choose
dual vectors

```lean
u : Fin m -> (Fin (d + 1) -> ℝ)
hdual : ∀ a b, MinkowskiSpace.minkowskiInner d (u a) (x (I b)) =
  if a = b then 1 else 0
```

This dual-vector step is not an assumption and must be proved before the
surjectivity theorem.  The Lean proof is finite-dimensional and explicit:

```lean
def sourceStdBasisVector
    (d : ℕ) (μ : Fin (d + 1)) : Fin (d + 1) -> ℝ :=
  Pi.single (M := fun _ : Fin (d + 1) => ℝ) μ (1 : ℝ)

theorem sourceStdBasis_sum
    (d : ℕ) (v : Fin (d + 1) -> ℝ) :
    (∑ μ : Fin (d + 1), v μ • sourceStdBasisVector d μ) = v

def minkowskiDualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) -> ℝ) ->ₗ[ℝ] ℝ) :
    Fin (d + 1) -> ℝ :=
  fun μ => MinkowskiSpace.metricSignature d μ *
    ell (sourceStdBasisVector d μ)

theorem minkowskiInner_dualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) -> ℝ) ->ₗ[ℝ] ℝ)
    (v : Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d
      (minkowskiDualVectorOfLinearFunctional d ell) v = ell v
```

The proof of the last theorem expands `v` in the standard coordinate basis.
Coordinatewise, avoid the local `NeZero d` side condition on
`MinkowskiSpace.metricSignature_mul_self` by splitting on `μ = 0` and
simplifying `MinkowskiSpace.metricSignature`; this proves
`η_μ * η_μ = 1` directly in all source dimensions.  Then rewrite
`ell (∑ μ, v μ • e_μ)` by `map_sum` and `map_smul`, and finish with
`sourceStdBasis_sum`.

For an independent selected family `e : Fin m -> Fin (d + 1) -> ℝ`, construct
the Kronecker duals by extending coordinate functionals from the span:

```lean
theorem exists_minkowski_dual_family_of_linearIndependent
    (d m : ℕ)
    {e : Fin m -> Fin (d + 1) -> ℝ}
    (hli : LinearIndependent ℝ e) :
    ∃ u : Fin m -> Fin (d + 1) -> ℝ,
      ∀ a b : Fin m,
        MinkowskiSpace.minkowskiInner d (u a) (e b) =
          if a = b then 1 else 0 := by
  let W : Submodule ℝ (Fin (d + 1) -> ℝ) :=
    Submodule.span ℝ (Set.range e)
  classical
  choose ell hell using
    fun a : Fin m =>
      LinearMap.exists_extend
        ((Finsupp.lapply a).comp hli.repr :
          W ->ₗ[ℝ] ℝ)
  refine ⟨fun a => minkowskiDualVectorOfLinearFunctional d (ell a), ?_⟩
  intro a b
  rw [minkowskiInner_dualVectorOfLinearFunctional]
  have hbW : (⟨e b, Submodule.subset_span ⟨b, rfl⟩⟩ : W) = _ := rfl
  have hell_apply :
      ell a (e b) =
        ((Finsupp.lapply a).comp hli.repr)
          (⟨e b, Submodule.subset_span ⟨b, rfl⟩⟩ : W) := by
    simpa using congrArg (fun L => L
      (⟨e b, Submodule.subset_span ⟨b, rfl⟩⟩ : W)) (hell a)
  rw [hell_apply, LinearMap.comp_apply, Finsupp.lapply_apply]
  rw [hli.repr_eq_single b
    (⟨e b, Submodule.subset_span ⟨b, rfl⟩⟩ : W) rfl]
  by_cases h : a = b
  · subst h
    simp
  · simp [h]
```

The final selected-row supplier is then immediate from the checked front-door
lemma:

```lean
theorem exists_minkowski_dual_sourceRows_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    ∃ u : Fin (min n (d + 1)) -> Fin (d + 1) -> ℝ,
      ∀ a b : Fin (min n (d + 1)),
        MinkowskiSpace.minkowskiInner d (u a) (x (I b)) =
          if a = b then 1 else 0
```

Then define the source variation by

```lean
selectedVar a := (1 / 2) •
  ∑ b : Fin m, A (I a) b • u b

residualVar r := ∑ a : Fin m,
  (A r a - MinkowskiSpace.minkowskiInner d (x r) (selectedVar a)) • u a

h r := if hr : r ∈ Set.range I
  then selectedVar ((Equiv.ofInjective I hI).symm ⟨r, hr⟩)
  else residualVar r
```

The proof should expose the two elementary calculation lemmas used here, not
bury them inside a tactic block:

```lean
theorem sourceRealGramDifferential_apply_eq_minkowskiInner
    (d n : ℕ)
    (x h : Fin n -> Fin (d + 1) -> ℝ)
    (i j : Fin n) :
    sourceRealGramDifferential d n x h i j =
      MinkowskiSpace.minkowskiInner d (h i) (x j) +
        MinkowskiSpace.minkowskiInner d (x i) (h j)

theorem minkowskiInner_sum_smul_dual_left
    (d m : ℕ)
    {u e : Fin m -> Fin (d + 1) -> ℝ}
    (hdual :
      ∀ a b : Fin m,
        MinkowskiSpace.minkowskiInner d (u a) (e b) =
          if a = b then 1 else 0)
    (coeff : Fin m -> ℝ) (a : Fin m) :
    MinkowskiSpace.minkowskiInner d
      (∑ b : Fin m, coeff b • u b) (e a) = coeff a
```

The first is just `Finset.sum_add_distrib` after unfolding the differential
and `minkowskiInner`; the second uses the linearity of
`v ↦ MinkowskiSpace.minkowskiInner d v (e a)`, `map_sum`, `map_smul`, the
dual identity, and the finite sum of Kronecker deltas.

The selected row calculation is:

```lean
have hselected_pair :
    ∀ a b : Fin m,
      MinkowskiSpace.minkowskiInner d (selectedVar a) (x (I b)) =
        (1 / 2) * A (I a) b := by
  intro a b
  unfold selectedVar
  rw [sourceMinkowskiInner_smul_left]
  rw [minkowskiInner_sum_smul_dual_left d m hdual]

have h_selected :
    ∀ a b : Fin m,
      sourceRealGramDifferential d n x h (I a) (I b) =
        A (I a) b := by
  intro a b
  rw [sourceRealGramDifferential_apply_eq_minkowskiInner]
  rw [h_at_selected a, h_at_selected b]
  rw [hselected_pair a b]
  rw [sourceMinkowskiInner_comm d (x (I a)) (selectedVar b),
    hselected_pair b a]
  have hsymAB :
      A (I b) a = A (I a) b :=
    (mem_sourceSelectedSymCoordSubspace.mp hA b a)
  nlinarith
```

The unselected row calculation is:

```lean
have hresidual_pair :
    ∀ r : Fin n, ∀ a : Fin m,
      MinkowskiSpace.minkowskiInner d (residualVar r) (x (I a)) =
        A r a - MinkowskiSpace.minkowskiInner d (x r) (selectedVar a) := by
  intro r a
  unfold residualVar
  rw [minkowskiInner_sum_smul_dual_left d m hdual]

have h_unselected :
    ∀ r : Fin n, r ∉ Set.range I ->
      ∀ a : Fin m,
        sourceRealGramDifferential d n x h r (I a) = A r a := by
  intro r hr a
  rw [sourceRealGramDifferential_apply_eq_minkowskiInner]
  rw [h_at_unselected r hr, h_at_selected a]
  rw [hresidual_pair r a]
  ring
```

In the range proof, split each row `r` by `by_cases hr : r ∈ Set.range I`.
In the selected case set
`c := (Equiv.ofInjective I hI).symm ⟨r, hr⟩`; use
`Equiv.apply_ofInjective_symm hI ⟨r, hr⟩` to rewrite `I c = r`, then apply
`h_selected c a`.  In the unselected case apply `h_unselected r hr a`.

For selected rows the block symmetry gives

```lean
dG_x(h) (I a) (I b) = A (I a) b.
```

For unselected rows the residual definition gives

```lean
dG_x(h) r (I a) = A r a.
```

Together these prove

```lean
LinearMap.range
  ((sourceSelectedGramCoord n m I).comp
    (sourceRealGramDifferential d n x))
= sourceSelectedSymCoordSubspace n m I
```

8. The selected-coordinate projection is injective on the range of the full
differential.  If two image variations have equal selected coordinates, then
for each `j : Fin n` use the coefficients from step 3:

```lean
x j = ∑ a, c j a • x (I a)
```

First reduce to the kernel statement.  It is enough to prove that, for a
variation `h`, if

```lean
hsel : sourceSelectedGramCoord n m I
  ((sourceRealGramDifferential d n x) h) = 0
```

then `sourceRealGramDifferential d n x h = 0`.  The coefficient supplier is a
separate checked finite-dimensional lemma:

```lean
theorem sourceRows_coefficients_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    ∃ c : Fin n -> Fin (min n (d + 1)) -> ℝ,
      ∀ r : Fin n,
        x r = ∑ a : Fin (min n (d + 1)), c r a • x (I a)
```

It follows from
`span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero` and
`Submodule.mem_span_range_iff_exists_fun`.

The kernel calculation uses the following linearity helpers:

```lean
theorem sourceMinkowskiInner_sum_smul_left
    (d m : ℕ)
    (coeff : Fin m -> ℝ)
    (u : Fin m -> Fin (d + 1) -> ℝ)
    (v : Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d
      (∑ a : Fin m, coeff a • u a) v =
      ∑ a : Fin m, coeff a *
        MinkowskiSpace.minkowskiInner d (u a) v

theorem sourceMinkowskiInner_sum_smul_right
    (d m : ℕ)
    (u : Fin (d + 1) -> ℝ)
    (coeff : Fin m -> ℝ)
    (v : Fin m -> Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d u
      (∑ a : Fin m, coeff a • v a) =
      ∑ a : Fin m, coeff a *
        MinkowskiSpace.minkowskiInner d u (v a)
```

For the kernel proof, write `e a := x (I a)` and

```lean
hApprox r := ∑ a, c r a • h (I a)
```

The selected-coordinate zero hypothesis gives

```lean
hzero_col : ∀ i a,
  sourceRealGramDifferential d n x h i (I a) = 0
```

and the selected block equations give, for every `j b`,

```lean
MinkowskiSpace.minkowskiInner d (h j - hApprox j) (x (I b)) = 0
```

because `hzero_col j b` says
`B(h j, e_b) + B(x j, h(I b)) = 0`, while the expansion of `x j`
and the equations `hzero_col (I a) b` give
`B(hApprox j, e_b) + B(x j, h(I b)) = 0`.

Then for arbitrary `i j`,

```lean
dG_x(h) i j
  = B(h i, x j) + B(x i, h j)
  = B(h i, x j) + B(x i, hApprox j)
  = ∑ a, c j a * dG_x(h) i (I a)
  = 0.
```

Here `B(x i, h j - hApprox j) = 0` follows by expanding `x i` in the selected
rows and using the just-proved orthogonality of `h j - hApprox j` to every
selected row.  This proves the kernel statement, and the injectivity theorem
follows by applying it to the difference of two representatives in
`LinearMap.range (sourceRealGramDifferential d n x)`.

Bilinearity then gives the useful displayed identity

```lean
dG_x(h) i j = ∑ a, c j a * dG_x(h) i (I a)
```

so all target coordinates agree.  Therefore the projection restricts to a
linear equivalence between

```lean
LinearMap.range (sourceRealGramDifferential d n x)
```

and `sourceSelectedSymCoordSubspace n m I`.

9. The rank theorem follows by finrank through that linear equivalence and the
checked arithmetic identity

```lean
n * m - (m * (m - 1)) / 2 = sourceGramExpectedDim d n
```

after unfolding `sourceGramExpectedDim`.

The Lean assembly should be explicit:

```lean
let L := sourceRealGramDifferential d n x
let P := sourceSelectedGramCoord n (min n (d + 1)) I
let S := sourceSelectedSymCoordSubspace n (min n (d + 1)) I

def rangeToSelectedSym :
    LinearMap.range L ->ₗ[ℝ] S :=
{ toFun := fun y =>
    ⟨P y, by
      rcases y.property with ⟨h, rfl⟩
      rw [← sourceSelectedGramCoord_comp_differential_range_eq
        d n hI hJ hminor]
      exact ⟨h, rfl⟩⟩,
  ... }

have hinj : Function.Injective rangeToSelectedSym := by
  intro y z hyz
  apply sourceSelectedGramCoord_injective_on_differential_range d n hI hJ hminor
  exact congrArg Subtype.val hyz

have hsurj : Function.Surjective rangeToSelectedSym := by
  intro A
  have hA :
      (A : Fin n -> Fin (min n (d + 1)) -> ℝ) ∈
        LinearMap.range (P.comp L) := by
    rw [sourceSelectedGramCoord_comp_differential_range_eq d n hI hJ hminor]
    exact A.property
  rcases hA with ⟨h, hh⟩
  refine ⟨⟨L h, ⟨h, rfl⟩⟩, ?_⟩
  ext i a
  exact congrFun (congrFun hh i) a

let e : LinearMap.range L ≃ₗ[ℝ] S :=
  LinearEquiv.ofBijective rangeToSelectedSym ⟨hinj, hsurj⟩

calc
  Module.finrank ℝ (LinearMap.range L)
      = Module.finrank ℝ S := e.finrank_eq
  _ = n * m - (m * (m - 1)) / 2 :=
      finrank_sourceSelectedSymCoordSubspace n m I hI
  _ = sourceGramExpectedDim d n := by
      simp [sourceGramExpectedDim, m]
```

The kernel calculation is equivalent and useful for rank-nullity:

1. variations in the annihilator of the selected span contribute
   `n * ((d + 1) - m)` kernel dimensions;
2. span-tangent variations `A` satisfying
   `B (A e_a) e_b + B e_a (A e_b) = 0` are the infinitesimal
   skew-adjoint endomorphisms of the selected span, of dimension
   `m * (m - 1) / 2`;
3. the total kernel dimension is
   `n * ((d + 1) - m) + m * (m - 1) / 2`;
4. rank-nullity gives the same rank formula.

Lean-facing theorem packet:

```lean
/-- The real source Gram map has the declared Frechet derivative. -/
theorem BHW.sourceRealMinkowskiGram_hasFDerivAt
    (d n : ℕ)
    (x : NPointDomain d n) :
    HasFDerivAt (BHW.sourceRealMinkowskiGram d n)
      (LinearMap.toContinuousLinearMap
        (BHW.sourceRealGramDifferential d n x)) x

/-- The real source Gram map is smooth; it is a polynomial in the source
coordinates. -/
theorem BHW.contDiff_sourceRealMinkowskiGram
    (d n : ℕ) :
    ContDiff ℝ ⊤ (BHW.sourceRealMinkowskiGram d n)

/-- Selected source rows from a nonzero coordinate minor are linearly
independent. -/
theorem BHW.linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    LinearIndependent ℝ (fun a => x (I a))

/-- Selected source rows from a nonzero maximal minor span the whole source
configuration span. -/
theorem BHW.span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    Submodule.span ℝ (Set.range (fun a => x (I a))) =
      BHW.sourceConfigurationSpan d n x

def BHW.sourceSelectedGramCoord
    (n m : ℕ) (I : Fin m -> Fin n) :
    (Fin n -> Fin n -> ℝ) →ₗ[ℝ] (Fin n -> Fin m -> ℝ)

def BHW.sourceSelectedSymCoordSubspace
    (n m : ℕ) (I : Fin m -> Fin n) :
    Submodule ℝ (Fin n -> Fin m -> ℝ)

def BHW.sourceStdBasisVector
    (d : ℕ) (μ : Fin (d + 1)) : Fin (d + 1) -> ℝ

theorem BHW.sourceStdBasis_sum
    (d : ℕ) (v : Fin (d + 1) -> ℝ) :
    (∑ μ : Fin (d + 1), v μ • BHW.sourceStdBasisVector d μ) = v

def BHW.minkowskiDualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) -> ℝ) ->ₗ[ℝ] ℝ) :
    Fin (d + 1) -> ℝ

theorem BHW.minkowskiInner_dualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) -> ℝ) ->ₗ[ℝ] ℝ)
    (v : Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d
      (BHW.minkowskiDualVectorOfLinearFunctional d ell) v = ell v

theorem BHW.exists_minkowski_dual_family_of_linearIndependent
    (d m : ℕ)
    {e : Fin m -> Fin (d + 1) -> ℝ}
    (hli : LinearIndependent ℝ e) :
    ∃ u : Fin m -> Fin (d + 1) -> ℝ,
      ∀ a b : Fin m,
        MinkowskiSpace.minkowskiInner d (u a) (e b) =
          if a = b then 1 else 0

theorem BHW.exists_minkowski_dual_sourceRows_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    ∃ u : Fin (min n (d + 1)) -> Fin (d + 1) -> ℝ,
      ∀ a b : Fin (min n (d + 1)),
        MinkowskiSpace.minkowskiInner d (u a) (x (I b)) =
          if a = b then 1 else 0

abbrev BHW.sourceSelectedUpperPair (m : ℕ) :=
  {p : Fin m × Fin m // p.1 < p.2}

def BHW.sourceSelectedSkewCoord
    (n m : ℕ) (I : Fin m -> Fin n) :
    (Fin n -> Fin m -> ℝ) →ₗ[ℝ]
      (BHW.sourceSelectedUpperPair m -> ℝ)

theorem BHW.sourceSelectedSkewCoord_ker
    (n m : ℕ) (I : Fin m -> Fin n) :
    LinearMap.ker (BHW.sourceSelectedSkewCoord n m I) =
      BHW.sourceSelectedSymCoordSubspace n m I

theorem BHW.sourceSelectedSkewCoord_surjective
    (n m : ℕ) (I : Fin m -> Fin n)
    (hI : Function.Injective I) :
    Function.Surjective (BHW.sourceSelectedSkewCoord n m I)

theorem BHW.card_sourceSelectedUpperPair
    (m : ℕ) :
    Fintype.card (BHW.sourceSelectedUpperPair m) =
      m * (m - 1) / 2

theorem BHW.finrank_sourceSelectedSymCoordSubspace
    (n m : ℕ)
    (I : Fin m -> Fin n)
    (hI : Function.Injective I) :
    Module.finrank ℝ
      (BHW.sourceSelectedSymCoordSubspace n m I) =
      n * m - (m * (m - 1)) / 2

theorem BHW.sourceSelectedGramCoord_comp_differential_range_eq
    (d n : ℕ)
    {x : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    LinearMap.range
      ((BHW.sourceSelectedGramCoord n (min n (d + 1)) I).comp
        (BHW.sourceRealGramDifferential d n x)) =
      BHW.sourceSelectedSymCoordSubspace n (min n (d + 1)) I

theorem BHW.sourceSelectedGramCoord_injective_on_differential_range
    (d n : ℕ)
    {x : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    Function.Injective
      (fun y : LinearMap.range (BHW.sourceRealGramDifferential d n x) =>
        (BHW.sourceSelectedGramCoord n (min n (d + 1)) I) y)

/-- Rank theorem in the nonzero-minor coordinates.  This is the theorem to
prove first; the `SourceGramRegularAt` version is its corollary. -/
theorem BHW.sourceRealGramDifferential_rank_of_exists_nonzero_minor
    (d n : ℕ)
    {x : NPointDomain d n}
    (hminor :
      ∃ I : Fin (min n (d + 1)) -> Fin n,
        Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) -> Fin (d + 1),
          Function.Injective J ∧
          BHW.sourceRegularMinor d n I J x ≠ 0) :
    Module.finrank ℝ
      (LinearMap.range (BHW.sourceRealGramDifferential d n x)) =
      BHW.sourceGramExpectedDim d n

/-- Kernel dimension of the Gram differential at a regular point.  The kernel
contains both normal-annihilator variations and infinitesimal skew-adjoint
span rotations. -/
theorem BHW.sourceRealGramDifferential_kernel_finrank_of_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    Module.finrank ℝ
      (LinearMap.ker (BHW.sourceRealGramDifferential d n x)) =
      n * ((d + 1) - min n (d + 1)) +
        (min n (d + 1)) * ((min n (d + 1)) - 1) / 2

theorem BHW.sourceRealGramDifferential_rank_of_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    Module.finrank ℝ
      (LinearMap.range (BHW.sourceRealGramDifferential d n x)) =
      BHW.sourceGramExpectedDim d n

/-- Complexifying a real regular source configuration remains regular.  Prove
this through the already checked nonzero-minor characterization, after casting
the nonzero real determinant to a nonzero complex determinant. -/
theorem BHW.sourceComplex_regular_of_real_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    BHW.SourceComplexGramRegularAt d n (BHW.realEmbed x)

/-- At a real regular point, the complex tangent of the complex scalar-product
variety is exactly the complex span of the real tangent. -/
theorem BHW.sourceComplexifiedRealTangentEqualsComplexTangent_of_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    BHW.SourceComplexifiedRealTangentEqualsComplexTangent d n
      (BHW.sourceRealMinkowskiGram d n x)
```

The immediate algebraic implementation subpacket is now split across the
stable regular-locus file `SourceExtension.lean` and the post-cleanup companion
`SourceRegularRank.lean`:

```lean
def BHW.sourceRealGramDifferential
    (d n : ℕ)
    (x : Fin n -> Fin (d + 1) -> ℝ) :
    (Fin n -> Fin (d + 1) -> ℝ) →ₗ[ℝ]
      (Fin n -> Fin n -> ℝ) :=
{ toFun := fun h i j =>
    ∑ μ : Fin (d + 1),
      MinkowskiSpace.metricSignature d μ *
        (h i μ * x j μ + x i μ * h j μ)
  map_add' := by
    intro h₁ h₂
    ext i j
    simp [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c h
    ext i j
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
    apply Finset.sum_congr rfl
    intro μ _
    ring }

def BHW.sourceComplexGramDifferential
    (d n : ℕ)
    (z : Fin n -> Fin (d + 1) -> ℂ) :
    (Fin n -> Fin (d + 1) -> ℂ) →ₗ[ℂ]
      (Fin n -> Fin n -> ℂ) :=
{ toFun := fun h i j =>
    ∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) *
        (h i μ * z j μ + z i μ * h j μ)
  map_add' := by
    intro h₁ h₂
    ext i j
    simp [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c h
    ext i j
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
    apply Finset.sum_congr rfl
    intro μ _
    ring }

theorem BHW.sourceRealMinkowskiGram_hasFDerivAt
    (d n : ℕ)
    (x : Fin n -> Fin (d + 1) -> ℝ) :
    HasFDerivAt (BHW.sourceRealMinkowskiGram d n)
      (LinearMap.toContinuousLinearMap
        (BHW.sourceRealGramDifferential d n x)) x

theorem BHW.sourceComplexGramDifferential_realEmbed
    (d n : ℕ)
    (x h : Fin n -> Fin (d + 1) -> ℝ) :
    BHW.sourceComplexGramDifferential d n (BHW.realEmbed x)
        (BHW.realEmbed h) =
      BHW.sourceRealGramComplexify n
        ((BHW.sourceRealGramDifferential d n x) h) := by
  ext i j
  simp [BHW.sourceComplexGramDifferential,
    BHW.sourceRealGramDifferential, BHW.sourceRealGramComplexify,
    BHW.realEmbed]

theorem BHW.contDiff_sourceRealMinkowskiGram
    (d n : ℕ) :
    ContDiff ℝ ⊤ (BHW.sourceRealMinkowskiGram d n) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  unfold BHW.sourceRealMinkowskiGram
  apply ContDiff.sum
  intro μ _
  exact ((contDiff_const.mul (contDiff_apply_apply ℝ ℝ i μ)).mul
    (contDiff_apply_apply ℝ ℝ j μ))

theorem BHW.linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    LinearIndependent ℝ (fun a : Fin (min n (d + 1)) => x (I a))

theorem BHW.span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    Submodule.span ℝ
        (Set.range (fun a : Fin (min n (d + 1)) => x (I a))) =
      BHW.sourceConfigurationSpan d n x

def BHW.sourceSelectedGramCoord
    (n m : ℕ) (I : Fin m -> Fin n) :
    (Fin n -> Fin n -> ℝ) →ₗ[ℝ] (Fin n -> Fin m -> ℝ)

def BHW.sourceSelectedSymCoordSubspace
    (n m : ℕ) (I : Fin m -> Fin n) :
    Submodule ℝ (Fin n -> Fin m -> ℝ)

theorem BHW.sourceRealGramDifferential_symm
    (d n : ℕ)
    (x h : Fin n -> Fin (d + 1) -> ℝ)
    (i j : Fin n) :
    BHW.sourceRealGramDifferential d n x h i j =
      BHW.sourceRealGramDifferential d n x h j i

theorem BHW.sourceSelectedGramCoord_differential_mem
    (d n : ℕ)
    (x h : Fin n -> Fin (d + 1) -> ℝ)
    {m : ℕ} (I : Fin m -> Fin n) :
    BHW.sourceSelectedGramCoord n m I
        ((BHW.sourceRealGramDifferential d n x) h) ∈
      BHW.sourceSelectedSymCoordSubspace n m I

theorem BHW.minkowskiInner_dualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) -> ℝ) ->ₗ[ℝ] ℝ)
    (v : Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d
      (BHW.minkowskiDualVectorOfLinearFunctional d ell) v = ell v

theorem BHW.exists_minkowski_dual_family_of_linearIndependent
    (d m : ℕ)
    {e : Fin m -> Fin (d + 1) -> ℝ}
    (hli : LinearIndependent ℝ e) :
    ∃ u : Fin m -> Fin (d + 1) -> ℝ,
      ∀ a b : Fin m,
        MinkowskiSpace.minkowskiInner d (u a) (e b) =
          if a = b then 1 else 0

theorem BHW.exists_minkowski_dual_sourceRows_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    ∃ u : Fin (min n (d + 1)) -> Fin (d + 1) -> ℝ,
      ∀ a b : Fin (min n (d + 1)),
        MinkowskiSpace.minkowskiInner d (u a) (x (I b)) =
          if a = b then 1 else 0

theorem BHW.sourceMinkowskiInner_comm
    (d : ℕ) (x y : Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d x y =
      MinkowskiSpace.minkowskiInner d y x

theorem BHW.sourceMinkowskiInner_smul_left
    (d : ℕ) (c : ℝ) (x y : Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d (c • x) y =
      c * MinkowskiSpace.minkowskiInner d x y

theorem BHW.sourceRealGramDifferential_apply_eq_minkowskiInner
    (d n : ℕ)
    (x h : Fin n -> Fin (d + 1) -> ℝ)
    (i j : Fin n) :
    BHW.sourceRealGramDifferential d n x h i j =
      MinkowskiSpace.minkowskiInner d (h i) (x j) +
        MinkowskiSpace.minkowskiInner d (x i) (h j)

theorem BHW.minkowskiInner_sum_smul_dual_left
    (d m : ℕ)
    {u e : Fin m -> Fin (d + 1) -> ℝ}
    (hdual :
      ∀ a b : Fin m,
        MinkowskiSpace.minkowskiInner d (u a) (e b) =
          if a = b then 1 else 0)
    (coeff : Fin m -> ℝ) (a : Fin m) :
    MinkowskiSpace.minkowskiInner d
      (∑ b : Fin m, coeff b • u b) (e a) = coeff a

theorem BHW.sourceMinkowskiInner_sum_smul_left
    (d m : ℕ)
    (coeff : Fin m -> ℝ)
    (u : Fin m -> Fin (d + 1) -> ℝ)
    (v : Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d
      (∑ a : Fin m, coeff a • u a) v =
      ∑ a : Fin m, coeff a *
        MinkowskiSpace.minkowskiInner d (u a) v

theorem BHW.sourceMinkowskiInner_sum_smul_right
    (d m : ℕ)
    (u : Fin (d + 1) -> ℝ)
    (coeff : Fin m -> ℝ)
    (v : Fin m -> Fin (d + 1) -> ℝ) :
    MinkowskiSpace.minkowskiInner d u
      (∑ a : Fin m, coeff a • v a) =
      ∑ a : Fin m, coeff a *
        MinkowskiSpace.minkowskiInner d u (v a)

theorem BHW.sourceRows_coefficients_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    ∃ c : Fin n -> Fin (min n (d + 1)) -> ℝ,
      ∀ r : Fin n,
        x r = ∑ a : Fin (min n (d + 1)), c r a • x (I a)

theorem BHW.sourceRealGramDifferential_eq_zero_of_selectedGramCoord_eq_zero
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0)
    {h : Fin n -> Fin (d + 1) -> ℝ}
    (hsel :
      BHW.sourceSelectedGramCoord n (min n (d + 1)) I
        ((BHW.sourceRealGramDifferential d n x) h) = 0) :
    (BHW.sourceRealGramDifferential d n x) h = 0

theorem BHW.sourceSelectedGramCoord_comp_differential_range_eq
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    LinearMap.range
      ((BHW.sourceSelectedGramCoord n (min n (d + 1)) I).comp
        (BHW.sourceRealGramDifferential d n x)) =
      BHW.sourceSelectedSymCoordSubspace n (min n (d + 1)) I

theorem BHW.sourceSelectedGramCoord_injective_on_differential_range
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    Function.Injective
      (fun y : LinearMap.range (BHW.sourceRealGramDifferential d n x) =>
        (BHW.sourceSelectedGramCoord n (min n (d + 1)) I) y)
```

This subpacket now closes the selected-coordinate rank calculation itself:
the differential range is linearly equivalent to the symmetric
selected-coordinate subspace, the strict-upper skew map gives that subspace's
codimension, and `sourceRealGramDifferential_rank_of_regular` is checked.  It
does not yet assert a local submersion chart, real-environment uniqueness, or
any OS-side conclusion.  The next proof-doc stage is the finite-dimensional
augmented inverse-function chart and the real-environment supplier built from
it.

The next chart stage must be stated as a relative-openness theorem, not as an
affine tangent-plane theorem.  The tempting statement

```lean
∀ r near 0 in LinearMap.range (sourceRealGramDifferential d n x0),
  ∃ y near x0,
    sourceRealMinkowskiGram d n y =
      sourceRealMinkowskiGram d n x0 + r
```

is too strong in general: the Hall-Wightman scalar-product locus is a curved
rank-bounded variety, so a regular image is locally a graph over its tangent
coordinates, not literally an open subset of the affine tangent plane.  The
correct output is that the Gram image of a small regular source patch is
relatively open in `sourceRealGramVariety d n`.

Use the selected-coordinate map as the submersion coordinate.  For
`m = min n (d + 1)` and a fixed nonzero minor `I,J` at `x0`, define the
codomain-restricted differential

```lean
def BHW.sourceSelectedGramDifferentialToSym
    (d n m : ℕ)
    (x : NPointDomain d n)
    (I : Fin m -> Fin n) :
    NPointDomain d n →ₗ[ℝ]
      BHW.sourceSelectedSymCoordSubspace n m I :=
{ toFun := fun h =>
    ⟨BHW.sourceSelectedGramCoord n m I
      ((BHW.sourceRealGramDifferential d n x) h),
     BHW.sourceSelectedGramCoord_differential_mem d n x h I⟩,
  ... }

theorem BHW.sourceSelectedGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    Function.Surjective
      (BHW.sourceSelectedGramDifferentialToSym d n
        (min n (d + 1)) x I)

theorem BHW.sourceSelectedGramDifferentialToSym_ker_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    LinearMap.ker
      (BHW.sourceSelectedGramDifferentialToSym d n
        (min n (d + 1)) x I) =
      LinearMap.ker (BHW.sourceRealGramDifferential d n x)
```

The first theorem is exactly the checked range equality, but with the
codomain already restricted to the symmetric selected-coordinate subspace
needed by mathlib's implicit-function theorem.  The second theorem says this
selected submersion has the same infinitesimal fibers as the full Gram map.

Then define the selected Gram coordinate map into that subspace:

```lean
def BHW.sourceSelectedRealGramMap
    (d n m : ℕ)
    (I : Fin m -> Fin n) :
    NPointDomain d n ->
      BHW.sourceSelectedSymCoordSubspace n m I :=
  fun x =>
    ⟨BHW.sourceSelectedGramCoord n m I
        (BHW.sourceRealMinkowskiGram d n x),
     by
       intro a b
       simp [BHW.sourceSelectedGramCoord,
         BHW.sourceRealMinkowskiGram_symm]⟩

theorem BHW.sourceSelectedRealGramMap_hasStrictFDerivAt
    (d n m : ℕ)
    (I : Fin m -> Fin n)
    (x : NPointDomain d n) :
    HasStrictFDerivAt
      (BHW.sourceSelectedRealGramMap d n m I)
      (LinearMap.toContinuousLinearMap
        (BHW.sourceSelectedGramDifferentialToSym d n m x I)) x
```

This proof uses `contDiff_sourceRealMinkowskiGram` and
`ContDiff.hasStrictFDerivAt`, then codomain-restricts the derivative to the
selected symmetric subspace.

For a nonzero minor at `x0`, apply mathlib's finite-dimensional implicit
function theorem

```lean
HasStrictFDerivAt.implicitToOpenPartialHomeomorph
```

to `sourceSelectedRealGramMap d n m I`.  Its target is

```lean
BHW.sourceSelectedSymCoordSubspace n m I ×
  LinearMap.ker
    (BHW.sourceSelectedGramDifferentialToSym d n m x0 I)
```

and the first component is definitionally the selected Gram coordinate map.
The minor nonvanishing condition is open, so shrink the source to the same
minor chart; on that chart all derivatives have the same selected-coordinate
rank and the same kernel as the full Gram differential.

The constant-rank step is then the finite-dimensional Hall-Wightman argument
in these selected coordinates.  Do **not** prove vertical constancy by
differentiating the implicit inverse along a vertical path: mathlib's current
implicit-function interface exposes the inverse derivative at the base point,
not on a whole local product neighborhood.  The faithful and Lean-ready route
is algebraic:

1. let `e` be the open partial homeomorphism from the implicit theorem;
2. for each selected coordinate `r` near the base value, define the source
   section `s r := e.symm (r, 0)`;
3. prove the finite selected-coordinate uniqueness theorem: on a fixed
   nonzero selected-minor chart, equality of selected Gram coordinates implies
   equality of the full Gram matrices;
4. apply that theorem to `y` and `s ((e y).1)`.  The first-coordinate identity
   for `e` gives equality of selected coordinates, and the source has been
   shrunk to the same nonzero-minor chart, so the full Gram values agree;
5. therefore the local Gram image is exactly
   `{sourceRealMinkowskiGram d n (s r) | r ∈ R}` for an open selected
   coordinate set `R`;
6. this set is relatively open in `sourceRealGramVariety d n`, with selected
   coordinates as its local chart.  No assertion is made that it is affine in
   the ambient full matrix space.

The selected-coordinate uniqueness theorem is now checked in Lean:

```lean
theorem BHW.sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x y : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor_x : BHW.sourceRegularMinor d n I J x ≠ 0)
    (hminor_y : BHW.sourceRegularMinor d n I J y ≠ 0)
    (hsel :
      BHW.sourceSelectedGramCoord n (min n (d + 1)) I
          (BHW.sourceRealMinkowskiGram d n x) =
        BHW.sourceSelectedGramCoord n (min n (d + 1)) I
          (BHW.sourceRealMinkowskiGram d n y)) :
    BHW.sourceRealMinkowskiGram d n x =
      BHW.sourceRealMinkowskiGram d n y
```

Proof transcript:

* Set `m = min n (d + 1)`.
* Case `hn : n ≤ d + 1`.  Then `m = n`, so the injective map
  `I : Fin m -> Fin n` is surjective after the cardinality rewrite.  For any
  `i j : Fin n`, choose `a : Fin m` with `I a = j`.  Evaluating `hsel` at
  `(i,a)` gives
  `sourceRealMinkowskiGram d n x i j =
   sourceRealMinkowskiGram d n y i j`.
  Extensionality closes the matrix equality.  This case uses no
  nondegeneracy of the restricted Minkowski form.
* Case `hD : d + 1 ≤ n`.  Then `m = d + 1`.  The nonzero minors make both
  selected families `x ∘ I` and `y ∘ I` bases of the full source spacetime.
  Use `span_sourceRows_eq_sourceConfigurationSpan_of_sourceRegularMinor_ne_zero`
  and the dimension squeeze, or equivalently the already checked
  `linearIndependent_sourceRows_of_sourceRegularMinor_ne_zero` plus
  `Module.finrank_fin_fun`, to get

  ```lean
  Submodule.span ℝ (Set.range (fun a : Fin m => x (I a))) = ⊤
  Submodule.span ℝ (Set.range (fun a : Fin m => y (I a))) = ⊤
  ```

* Add the local nondegeneracy support lemma:

  ```lean
  theorem BHW.sourceMinkowskiInner_left_nonDegenerate
      (d : ℕ) {w : Fin (d + 1) -> ℝ}
      (horth :
        ∀ v : Fin (d + 1) -> ℝ,
          MinkowskiSpace.minkowskiInner d w v = 0) :
      w = 0
  ```

  Proof: test `horth` on `sourceStdBasisVector d μ`; the resulting scalar is
  `MinkowskiSpace.metricSignature d μ * w μ`, and the signature entry is
  `1` for `μ = 0` and `-1` otherwise.
* Add the span version:

  ```lean
  theorem BHW.sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family
      (d m : ℕ)
      {e : Fin m -> Fin (d + 1) -> ℝ}
      (hspan :
        Submodule.span ℝ (Set.range e) = ⊤)
      {w : Fin (d + 1) -> ℝ}
      (horth :
        ∀ a : Fin m,
          MinkowskiSpace.minkowskiInner d w (e a) = 0) :
      w = 0
  ```

  Proof: define the right-linear functional
  `v ↦ MinkowskiSpace.minkowskiInner d w v`; it vanishes on the generating
  set, hence on its span, hence on `⊤`; then use
  `sourceMinkowskiInner_left_nonDegenerate`.
* In the full-spacetime case, choose coefficients `c_x r a` expressing
  `x r` in the selected `x`-rows, using
  `sourceRows_coefficients_of_sourceRegularMinor_ne_zero`.  For each `r`,
  define

  ```lean
  yApprox r := ∑ a : Fin m, c_x r a • y (I a)
  ```

  Evaluating `hsel` on selected block entries proves
  `MinkowskiSpace.minkowskiInner d (y r - yApprox r) (y (I b)) = 0` for all
  `b`.  Since the selected `y`-rows span `⊤`, the span nondegeneracy lemma gives
  `y r = yApprox r`.
* Now compute, for arbitrary `r s`,

  ```lean
  sourceRealMinkowskiGram d n x r s
    = ∑ a, c_x s a *
        sourceRealMinkowskiGram d n x r (I a)
    = ∑ a, c_x s a *
        sourceRealMinkowskiGram d n y r (I a)
    = sourceRealMinkowskiGram d n y r s
  ```

  The first and last equalities use the coefficient expansions and
  `sourceMinkowskiInner_sum_smul_right`; the middle equality is `hsel`.
  Extensionality closes the theorem.  The production proof also checks the
  support lemmas `sourceRealMinkowskiGram_apply_eq_minkowskiInner`,
  `sourceMinkowskiInner_add_right`, `sourceMinkowskiInner_smul_right`,
  `sourceMinkowskiInner_left_nonDegenerate`,
  `sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family`,
  `sourceSelectedIndex_surjective_of_le`, and
  `sourceSelectedRows_span_top_of_sourceRegularMinor_ne_zero`.

Lean-facing local-chart packet:

```lean
theorem BHW.sourceSelectedRealGramMap_implicit_chart_of_nonzero_minor
    (d n : ℕ)
    {x0 : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (NPointDomain d n)
        (BHW.sourceSelectedSymCoordSubspace n (min n (d + 1)) I ×
          LinearMap.ker
            (BHW.sourceSelectedGramDifferentialToSym d n
              (min n (d + 1)) x0 I)),
      x0 ∈ e.source ∧
      e x0 =
        (BHW.sourceSelectedRealGramMap d n (min n (d + 1)) I x0, 0) ∧
      ∀ x ∈ e.source,
        (e x).1 =
          BHW.sourceSelectedRealGramMap d n (min n (d + 1)) I x

theorem BHW.sourceRealGramMap_constant_on_selectedVerticalFibers
    (d n : ℕ)
    {x0 : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (NPointDomain d n)
        (BHW.sourceSelectedSymCoordSubspace n (min n (d + 1)) I ×
          LinearMap.ker
            (BHW.sourceSelectedGramDifferentialToSym d n
              (min n (d + 1)) x0 I)),
      x0 ∈ e.source ∧
      ∃ U : Set (NPointDomain d n),
        IsOpen U ∧ x0 ∈ U ∧ U ⊆ e.source ∧
        (∀ x ∈ U, BHW.sourceRegularMinor d n I J x ≠ 0) ∧
        ∀ y ∈ U, ∀ z ∈ U,
          (e y).1 = (e z).1 ->
          BHW.sourceRealMinkowskiGram d n y =
            BHW.sourceRealMinkowskiGram d n z

theorem BHW.sourceRealGramMap_localRelOpenImage_of_regular
    (d n : ℕ)
    {x0 : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x0) :
    ∃ U : Set (NPointDomain d n),
      IsOpen U ∧ x0 ∈ U ∧
      ∃ O : Set (Fin n -> Fin n -> ℝ),
        BHW.sourceRealMinkowskiGram d n x0 ∈ O ∧
        BHW.IsRelOpenInSourceRealGramVariety d n O ∧
        O ⊆ BHW.sourceRealMinkowskiGram d n '' U ∧
        ∀ G ∈ O, ∃ x ∈ U,
          BHW.SourceGramRegularAt d n x ∧
          BHW.sourceRealMinkowskiGram d n x = G
```

For the Hall-Wightman real-environment supplier, the usable form is the
open-neighborhood variant:

```lean
theorem BHW.sourceRealGramMap_localRelOpenImage_in_open_of_regular
    (d n : ℕ)
    {x0 : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x0)
    {V : Set (NPointDomain d n)}
    (hV_open : IsOpen V)
    (hx0V : x0 ∈ V) :
    ∃ U : Set (NPointDomain d n),
      IsOpen U ∧ x0 ∈ U ∧ U ⊆ V ∧
      ∃ O : Set (Fin n -> Fin n -> ℝ),
        BHW.sourceRealMinkowskiGram d n x0 ∈ O ∧
        BHW.IsRelOpenInSourceRealGramVariety d n O ∧
        O ⊆ BHW.sourceRealMinkowskiGram d n '' U ∧
        ∀ G ∈ O, ∃ x ∈ U,
          BHW.SourceGramRegularAt d n x ∧
          BHW.sourceRealMinkowskiGram d n x = G
```

Its proof is the same selected-coordinate chart proof, with the source patch
shrunk from `e.source ∩ {minor ≠ 0}` to
`e.source ∩ {minor ≠ 0} ∩ V`.  This is not a wrapper: it is the exact source
locality needed later to force the real-environment witnesses to stay inside
the user's chosen Jost/open patch.  The old theorem is recovered by taking
`V = Set.univ`.

The vertical-constancy theorem immediately above is now checked too.  Its proof
chooses the implicit chart `e` from
`sourceSelectedRealGramMap_implicit_chart_of_nonzero_minor`, sets
`U = e.source ∩ {x | sourceRegularMinor d n I J x ≠ 0}`, uses `e.open_source`
and `continuous_sourceRegularMinor` for openness, and converts
`(e y).1 = (e z).1` into equality of selected Gram coordinates via the
first-coordinate identity of the chart.  The checked algebraic uniqueness
theorem then gives equality of full Gram matrices.

One hidden point remains before the relative-openness theorem is Lean-ready:
relative openness is a statement in the **Gram variety**, not merely in the
source chart.  If a nearby Gram matrix `G` lies in
`sourceRealGramVariety d n`, Lean only gives an arbitrary realization
`G = sourceRealMinkowskiGram d n y`; this realization `y` need not already lie
in the same nonzero-minor source patch `U`.  The source-chart vertical
constancy theorem therefore is not enough by itself.  The missing algebraic
bridge is that selected coordinates equal to those of one regular chart point
determine the full Gram matrix for any realization in the variety.

The required proof packet is:

```lean
theorem BHW.sourceSelectedGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop
    (d n : ℕ)
    {x y : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hminor_x : BHW.sourceRegularMinor d n I J x ≠ 0)
    (hspan_y :
      Submodule.span ℝ
        (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤)
    (hsel :
      BHW.sourceSelectedGramCoord n (min n (d + 1)) I
          (BHW.sourceRealMinkowskiGram d n x) =
        BHW.sourceSelectedGramCoord n (min n (d + 1)) I
          (BHW.sourceRealMinkowskiGram d n y)) :
    BHW.sourceRealMinkowskiGram d n x =
      BHW.sourceRealMinkowskiGram d n y

theorem BHW.sourceSelectedRows_span_top_of_selectedGramCoord_eq_regular
    (d n : ℕ)
    {x y : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor_x : BHW.sourceRegularMinor d n I J x ≠ 0)
    (hsel :
      BHW.sourceSelectedGramCoord n (min n (d + 1)) I
          (BHW.sourceRealMinkowskiGram d n x) =
        BHW.sourceSelectedGramCoord n (min n (d + 1)) I
          (BHW.sourceRealMinkowskiGram d n y))
    (hD : d + 1 ≤ n) :
    Submodule.span ℝ
      (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤

theorem BHW.sourceSelectedGramCoord_eq_fullGram_eq_of_sourceRegularMinor_ne_zero_of_mem_variety
    (d n : ℕ)
    {x : NPointDomain d n}
    {G : Fin n -> Fin n -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hminor_x : BHW.sourceRegularMinor d n I J x ≠ 0)
    (hG : G ∈ BHW.sourceRealGramVariety d n)
    (hsel :
      BHW.sourceSelectedGramCoord n (min n (d + 1)) I
          (BHW.sourceRealMinkowskiGram d n x) =
        BHW.sourceSelectedGramCoord n (min n (d + 1)) I G) :
    BHW.sourceRealMinkowskiGram d n x = G
```

Proof transcript:

* The first theorem is the already checked selected-coordinate uniqueness
  proof with the right-hand nonzero-minor hypothesis replaced by the exact
  fact it used: the selected `y`-rows span the full source spacetime.  Choose
  coefficients `c_x r a` expressing each `x r` in the selected `x`-rows,
  define `yApprox r = ∑ a, c_x r a • y (I a)`, use selected-coordinate
  equality to show `y r - yApprox r` is orthogonal to every selected `y`-row,
  and use `hspan_y` plus
  `sourceMinkowskiInner_eq_zero_of_orthogonal_spanning_family` to get
  `y r = yApprox r`.  The final full-Gram calculation is the same finite sum
  expansion as in the checked theorem.
* For
  `sourceSelectedRows_span_top_of_selectedGramCoord_eq_regular`, assume
  `d + 1 ≤ n`, so `m = d + 1`.  The nonzero minor for `x` makes the selected
  `x`-rows span `⊤` and linearly independent.  To prove the selected `y`-rows
  linearly independent, take coefficients `c` with
  `∑ a, c a • y (I a) = 0`.  Pair this sum with each selected `y (I b)`.
  The selected Gram blocks of `x` and `y` agree by `hsel`, so
  `∑ a, c a • x (I a)` is orthogonal to every selected `x (I b)`.  Since the
  selected `x`-rows span `⊤`, nondegeneracy gives
  `∑ a, c a • x (I a) = 0`; linear independence of the selected `x`-rows gives
  `c = 0`.  Thus the selected `y`-rows are linearly independent, and their
  cardinality is `d + 1`, so their span is `⊤`.
* For the arbitrary-variety theorem, unfold
  `G ∈ sourceRealGramVariety d n` as `G = sourceRealMinkowskiGram d n y`.
  If `n ≤ d + 1`, then `I : Fin (min n (d+1)) -> Fin n` is surjective and
  selected columns are all columns.  If `d + 1 ≤ n`, first apply the previous
  span-transfer theorem to the arbitrary realization `y`, then apply
  `sourceSelectedGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop`.

This proof packet is now checked in
`BHWPermutation/SourceRegularRank.lean`: the arbitrary-variety uniqueness
bridge is no longer a documentation-only assumption.

With this algebraic bridge, the relative-open image proof becomes a direct
chart argument:

1. choose `I,J` from `exists_nonzero_minor_of_sourceGramRegularAt`;
2. apply `sourceRealGramMap_constant_on_selectedVerticalFibers` and keep the
   resulting source patch `U ⊆ e.source`;
3. define
   `T = e '' U` in the product chart and
   `R = Prod.fst '' T` in the selected symmetric-coordinate subspace;
4. `T` is open because `U` is open in `e.source` and `e` is an open partial
   homeomorphism; `R` is open because product projection is an open map;
5. choose an ambient open set `R0` whose preimage under the subtype inclusion
   is `R`; define
   `E0 = {G | sourceSelectedGramCoord n m I G ∈ R0}`;
6. set `O = E0 ∩ sourceRealGramVariety d n`.  This is relatively open by
   definition;
7. if `G ∈ O`, turn its selected coordinates into a subtype point of the
   selected symmetric-coordinate subspace using symmetry of real source Gram
   matrices.  Since that subtype point lies in `R`, choose `u ∈ U` with
   `(e u).1` equal to it.  The first-coordinate identity for `e` gives
   equality of selected coordinates for `u` and `G`, and the arbitrary-variety
   uniqueness theorem gives `sourceRealMinkowskiGram d n u = G`;
8. the same nonzero minor on `U` gives `SourceGramRegularAt d n u` by
   `sourceGramRegularAt_of_exists_nonzero_minor`.

The theorems `BHW.sourceRealGramMap_localRelOpenImage_in_open_of_regular` and
`BHW.sourceRealGramMap_localRelOpenImage_of_regular` are now checked in
`BHWPermutation/SourceRegularRank.lean`.  This is the precise local
constant-rank output needed for Hall-Wightman's real environment: it is a
relative-openness statement inside `sourceRealGramVariety d n`; it deliberately
does not claim affine openness in the tangent space.

```lean
theorem BHW.sourceRealGramMap_realEnvironmentAt_of_regular
    [NeZero d]
    (n : ℕ)
    {x0 : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x0)
    (hx0_jost : x0 ∈ BHW.JostSet d n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hx0V : x0 ∈ V) :
    ∃ O : Set (Fin n -> Fin n -> ℝ),
      O ⊆ BHW.sourceRealMinkowskiGram d n '' V ∧
      BHW.IsHWRealEnvironment d n O := by
  -- shrink `V` to `V0 = V ∩ JostSet d n ∩ regularLocus ∩ U`
  -- using `hV_open`, `BHW.isOpen_jostSet`,
  -- `BHW.isOpen_sourceGramRegularAt`, and the local chart domain `U`;
  -- apply `sourceRealGramMap_localRelOpenImage_of_regular` at `x0`;
  -- set `O = sourceRealMinkowskiGram d n '' V0`;
  -- `O ⊆ sourceRealMinkowskiGram d n '' V` is immediate from `V0 ⊆ V`;
  -- `relOpen` comes from the range-coordinate chart theorem above;
  -- `realized_by_jost` comes from the definition of `O`;
	  -- `maximal_totally_real` is
	  -- `sourceComplexifiedRealTangentEqualsComplexTangent_of_regular`
	  -- on the shrunken regular locus.
```

This theorem is now checked in
`BHWPermutation/SourceComplexTangent.lean`.  The implementation sets
`W = V ∩ JostSet d n`, applies
`sourceRealGramMap_localRelOpenImage_in_open_of_regular` to obtain a smaller
regular source patch `U ⊆ W` and a relatively open scalar-product image `O`,
then fills `IsHWRealEnvironment` as follows: nonemptiness from the base Gram
point, relative openness from the local image theorem, Jost realization from
`U ⊆ W`, and maximal-total-realness from
`sourceComplexifiedRealTangentEqualsComplexTangent_of_regular` at the regular
realizer supplied for each `G ∈ O`.

The complex tangent comparison is algebraic once the real and complex rank
theorems are available.  The first bridge lemma is now checked: complexifying
a real regular configuration remains regular.  The proof uses the nonzero
minor characterization of real regularity, casts the real determinant through
`RingHom.map_det Complex.ofRealHom`, obtains complex linear independence of
the same selected rows, and repeats the dimension squeeze in the complex
configuration span.  The differential bridge is also checked:

```lean
theorem BHW.sourceComplex_regular_of_real_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    BHW.SourceComplexGramRegularAt d n (BHW.realEmbed x)

theorem BHW.sourceComplexGramDifferential_realEmbed
    (d n : ℕ)
    (x h : NPointDomain d n) :
    BHW.sourceComplexGramDifferential d n (BHW.realEmbed x)
      (BHW.realEmbed h) =
      BHW.sourceRealGramComplexify n
        ((BHW.sourceRealGramDifferential d n x) h)

theorem BHW.sourceComplexGramDifferential_realEmbed_range_eq_complex_span
    (d n : ℕ)
    (x : NPointDomain d n) :
    LinearMap.range
        (BHW.sourceComplexGramDifferential d n (BHW.realEmbed x)) =
      Submodule.span ℂ
        (BHW.sourceRealGramComplexify n ''
          LinearMap.range (BHW.sourceRealGramDifferential d n x))

theorem BHW.sourceComplexifiedRealTangentEqualsComplexTangent_of_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    BHW.SourceComplexifiedRealTangentEqualsComplexTangent d n
      (BHW.sourceRealMinkowskiGram d n x)
```

The range-complexification theorem is now checked in
`BHWPermutation/SourceRegularRank.lean`.  Proof: for `⊆`, write an arbitrary
complex variation `h` as
`realEmbed (fun i μ => (h i μ).re) + Complex.I •
realEmbed (fun i μ => (h i μ).im)`, use complex-linearity of
`sourceComplexGramDifferential` and the checked
`sourceComplexGramDifferential_realEmbed` identity, and conclude membership in
the complex span.  For `⊇`, every complexified real differential value is the
complex differential of `realEmbed h`, so the generating set lies in the
complex range.

This by itself did **not** prove
`sourceComplexifiedRealTangentEqualsComplexTangent_of_regular`: the missing
obligation was the complex analogue of the selected-coordinate rank/local-chart
argument, showing that every regular complex realization over the same
complexified real Gram point has the same complex tangent image as the real
embedded regular point.  That obligation is now discharged in the following
finite-dimensional Hall-Wightman tangent packet, without adding assumptions.

The maximal-totally-real theorem is split into the following exact
Lean packet in the companion file
`BHWPermutation/SourceComplexTangent.lean`, leaving
`SourceRegularRank.lean` stable.

First, the easy inclusion: every complexified real tangent is a complex tangent.

```lean
theorem BHW.sourceRealGramTangent_complexify_subset_complexTangent
    (d n : ℕ)
    (G : Fin n -> Fin n -> ℝ) :
    BHW.sourceRealGramComplexify n ''
        BHW.sourceRealGramTangentSpaceAt d n G ⊆
      BHW.sourceComplexGramTangentSpaceAt d n
        (BHW.sourceRealGramComplexify n G)

theorem BHW.sourceRealGramTangent_complexified_span_le_complexTangent_span
    (d n : ℕ)
    (G : Fin n -> Fin n -> ℝ) :
    Submodule.span ℂ
        (BHW.sourceRealGramComplexify n ''
          BHW.sourceRealGramTangentSpaceAt d n G) ≤
      Submodule.span ℂ
        (BHW.sourceComplexGramTangentSpaceAt d n
          (BHW.sourceRealGramComplexify n G))
```

Proof transcript: unfold `sourceRealGramTangentSpaceAt`; a real tangent is
represented by a regular real source point `y` and a real variation `h`.
Use `sourceComplex_regular_of_real_regular y`, `sourceMinkowskiGram_realEmbed`,
and `sourceComplexGramDifferential_realEmbed` to represent its complexification
as a complex tangent at `realEmbed y`.  The span statement is
`Submodule.span_mono`.  These two theorems are now checked in
`BHWPermutation/SourceComplexTangent.lean`.

Second, the real embedded regular point already supplies a complex tangent
range contained in the complexified real-tangent span.

```lean
theorem BHW.sourceComplexGramDifferential_realEmbed_range_le_complexified_real_tangent_span_of_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    LinearMap.range
        (BHW.sourceComplexGramDifferential d n (BHW.realEmbed x)) ≤
      Submodule.span ℂ
        (BHW.sourceRealGramComplexify n ''
          BHW.sourceRealGramTangentSpaceAt d n
            (BHW.sourceRealMinkowskiGram d n x))
```

Proof transcript: rewrite the left side by
`sourceComplexGramDifferential_realEmbed_range_eq_complex_span`; every
generator `sourceRealGramComplexify n δG` with
`δG ∈ LinearMap.range (sourceRealGramDifferential d n x)` is in the real
tangent set by choosing the same regular point `x`, the proof `hreg`, and
`rfl` for the Gram value.  This theorem is now checked in
`BHWPermutation/SourceComplexTangent.lean`.

Third, the hard inclusion is exactly:

```lean
theorem BHW.sourceComplexGramTangent_subset_realEmbed_range_of_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    (hreg : BHW.SourceGramRegularAt d n x) :
    BHW.sourceComplexGramTangentSpaceAt d n
        (BHW.sourceRealGramComplexify n
          (BHW.sourceRealMinkowskiGram d n x)) ⊆
      LinearMap.range
        (BHW.sourceComplexGramDifferential d n (BHW.realEmbed x))
```

This is the genuine finite-dimensional Hall-Wightman tangent theorem.  It is
not a wrapper: it says that if a regular complex realization `z` has the same
complex Gram matrix as `realEmbed x`, then every first-order Gram variation at
`z` is also a first-order Gram variation at `realEmbed x`.

Lean-ready proof transcript for the hard theorem:

1. choose a nonzero real coordinate minor `I,J` for `x` from
   `exists_nonzero_minor_of_sourceGramRegularAt`.  Its complexification gives
   the same nonzero complex coordinate minor for `realEmbed x`;
2. for an arbitrary regular complex realization `z` with
   `sourceMinkowskiGram d n z =
    sourceRealGramComplexify n (sourceRealMinkowskiGram d n x)`, use the
   selected Gram equality to prove the selected `z (I a)` rows span
   `Fin (d+1) -> ℂ`.  This is the complex analogue of
   `sourceSelectedRows_span_top_of_selectedGramCoord_eq_regular`;
3. prove a complex cross-differential uniqueness theorem.  If
   `h : Fin n -> Fin (d+1) -> ℂ` is a variation at `z` and
   `k : Fin n -> Fin (d+1) -> ℂ` is a variation at `realEmbed x` with equal
   selected differential coordinates, then the full complex Gram
   differentials are equal.  The proof uses the Schur-complement/selected-row
   expansion

   ```lean
   δ r s =
     ∑ a, c s a * δ r (I a)
   + ∑ a, c r a * δ s (I a)
   - ∑ a, ∑ b, c r a * c s b * δ (I a) (I b)
   ```

   where the coefficients `c r a` express the rows of `realEmbed x` in the
   selected basis.  The selected coordinates determine the same coefficients
   for `z` because the two full Gram matrices agree and the selected `z` rows
   span;
4. use the complex selected-coordinate differential surjectivity at
   `realEmbed x` to choose `k` matching the selected coordinates of
   `sourceComplexGramDifferential d n z h`;
5. apply cross-differential uniqueness to show
   `sourceComplexGramDifferential d n z h =
    sourceComplexGramDifferential d n (realEmbed x) k`, hence membership in
   the real-embedded range.

Implementation-level helper order for the hard theorem:

```lean
def BHW.sourceComplexMinkowskiInner
    (d : ℕ) (u v : Fin (d + 1) -> ℂ) : ℂ :=
  ∑ μ : Fin (d + 1),
    (MinkowskiSpace.metricSignature d μ : ℂ) * u μ * v μ

theorem BHW.sourceMinkowskiGram_apply_eq_complexInner
    (d n : ℕ)
    (z : Fin n -> Fin (d + 1) -> ℂ)
    (i j : Fin n) :
    BHW.sourceMinkowskiGram d n z i j =
      BHW.sourceComplexMinkowskiInner d (z i) (z j)

theorem BHW.sourceComplexMinkowskiInner_left_nonDegenerate
    (d : ℕ) {w : Fin (d + 1) -> ℂ}
    (horth :
      ∀ v : Fin (d + 1) -> ℂ,
        BHW.sourceComplexMinkowskiInner d w v = 0) :
    w = 0

theorem BHW.sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family
    (d m : ℕ)
    {e : Fin m -> Fin (d + 1) -> ℂ}
    (hspan : Submodule.span ℂ (Set.range e) = ⊤)
    {w : Fin (d + 1) -> ℂ}
    (horth :
      ∀ a : Fin m,
        BHW.sourceComplexMinkowskiInner d w (e a) = 0) :
    w = 0
```

These are the complex analogues of the real Minkowski pairing lemmas already
checked in `SourceRegularRank.lean`.  They should be proved coordinatewise;
the nondegeneracy proof tests against `Pi.single μ 1` and uses that each
metric-signature entry is `1` or `-1`, hence nonzero in `ℂ`.

```lean
def BHW.sourceSelectedComplexGramCoord
    (n m : ℕ) (I : Fin m -> Fin n) :
    (Fin n -> Fin n -> ℂ) →ₗ[ℂ] (Fin n -> Fin m -> ℂ)

theorem BHW.sourceSelectedComplexGramCoord_apply
    ...

theorem BHW.sourceComplexRows_span_top_of_sameGram_real_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    {z : Fin n -> Fin (d + 1) -> ℂ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor_x : BHW.sourceRegularMinor d n I J x ≠ 0)
    (hzG :
      BHW.sourceMinkowskiGram d n z =
        BHW.sourceRealGramComplexify n
          (BHW.sourceRealMinkowskiGram d n x))
    (hD : d + 1 ≤ n) :
    Submodule.span ℂ
      (Set.range (fun a : Fin (min n (d + 1)) => z (I a))) = ⊤
```

Proof of the span-transfer theorem:

* the selected `realEmbed x` rows span `⊤` in the `d+1 ≤ n` case by the real
  nonzero minor and `sourceComplex_regular_of_real_regular`;
* if a coefficient vector annihilates the selected `z` rows, pair the sum with
  every selected `z (I b)`;
* rewrite the selected Gram block using `hzG` to obtain the same orthogonality
  relation for the corresponding combination of selected `realEmbed x` rows;
* nondegeneracy plus the selected `realEmbed x` span gives the real-embedded
  combination is zero;
* linear independence of the selected `realEmbed x` rows gives all
  coefficients zero, so selected `z` rows are linearly independent; since
  `m = d + 1`, their span is `⊤`.

```lean
theorem BHW.sourceComplexRows_eq_real_coefficients_of_sameGram_real_regular
    (d n : ℕ)
    {x : NPointDomain d n}
    {z : Fin n -> Fin (d + 1) -> ℂ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hminor_x : BHW.sourceRegularMinor d n I J x ≠ 0)
    (hzspan :
      Submodule.span ℂ
        (Set.range (fun a : Fin (min n (d + 1)) => z (I a))) = ⊤)
    (hzG :
      BHW.sourceMinkowskiGram d n z =
        BHW.sourceRealGramComplexify n
          (BHW.sourceRealMinkowskiGram d n x)) :
    ∃ c : Fin n -> Fin (min n (d + 1)) -> ℂ,
      (∀ r,
        BHW.realEmbed x r =
          ∑ a, c r a • BHW.realEmbed x (I a)) ∧
      (∀ r,
        z r = ∑ a, c r a • z (I a))
```

Proof: take the real coefficient family for `x` from
`sourceRows_coefficients_of_sourceRegularMinor_ne_zero` and cast it to `ℂ`.
The first expansion is by `realEmbed` and `map_sum/map_smul`.  For the second,
the residual
`z r - ∑ a, c r a • z (I a)` is orthogonal to every selected `z (I b)`:
the first term is `sourceMinkowskiGram d n z r (I b)`, and the expansion term
rewrites using the selected block of `hzG` and the real coefficient expansion
of `x r`.  Since selected `z` rows span, complex nondegeneracy kills the
residual.

```lean
theorem BHW.sourceComplexGramDifferential_selected_formula
    (d n m : ℕ)
    {z : Fin n -> Fin (d + 1) -> ℂ}
    {h : Fin n -> Fin (d + 1) -> ℂ}
    {I : Fin m -> Fin n}
    {c : Fin n -> Fin m -> ℂ}
    (hzexpand : ∀ r, z r = ∑ a, c r a • z (I a)) :
    ∀ r s,
      BHW.sourceComplexGramDifferential d n z h r s =
        (∑ a, c s a *
          BHW.sourceComplexGramDifferential d n z h r (I a)) +
        (∑ a, c r a *
          BHW.sourceComplexGramDifferential d n z h s (I a)) -
        (∑ a, ∑ b, c r a * c s b *
          BHW.sourceComplexGramDifferential d n z h (I a) (I b))
```

Proof: unfold the complex Gram differential as
`<h r,z s> + <z r,h s>`, rewrite `z r` and `z s` by `hzexpand`, use bilinearity
and symmetry of the complex Minkowski pairing, and cancel the selected-block
terms.  This is the exact differentiated Schur-complement formula; it is the
central algebraic identity of the hard tangent theorem.

```lean
theorem BHW.sourceComplexGramDifferential_eq_of_sameGram_real_regular_of_selected_eq
    (d n : ℕ)
    {x : NPointDomain d n}
    {z : Fin n -> Fin (d + 1) -> ℂ}
    {kx : Fin n -> Fin (d + 1) -> ℂ}
    {hz : Fin n -> Fin (d + 1) -> ℂ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hminor_x : BHW.sourceRegularMinor d n I J x ≠ 0)
    (hzG :
      BHW.sourceMinkowskiGram d n z =
        BHW.sourceRealGramComplexify n
          (BHW.sourceRealMinkowskiGram d n x))
    (hsel :
      BHW.sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (BHW.sourceComplexGramDifferential d n (BHW.realEmbed x) kx) =
        BHW.sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (BHW.sourceComplexGramDifferential d n z hz)) :
    BHW.sourceComplexGramDifferential d n (BHW.realEmbed x) kx =
      BHW.sourceComplexGramDifferential d n z hz
```

Proof: in the `n ≤ d+1` case, `I` is surjective, so selected columns are all
columns.  In the `d+1 ≤ n` case, use the same coefficient family `c` for
`realEmbed x` and `z` from the previous theorem, apply
`sourceComplexGramDifferential_selected_formula` to both sides, and rewrite
every selected entry by `hsel`.

The complex selected-coordinate differential surjectivity used here is checked
without adding a new complex-dual-basis route: split a symmetric complex
selected-coordinate target into real and imaginary parts, apply the already
checked real theorem
`sourceSelectedGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero`
to each part, and combine the two real variations as
`realEmbed hre + Complex.I • realEmbed him`.

```lean
theorem BHW.sourceSelectedComplexGramDifferential_surjective_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : NPointDomain d n}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0)
    {A : Fin n -> Fin (min n (d + 1)) -> ℂ}
    (hA : ∀ a b : Fin (min n (d + 1)), A (I a) b = A (I b) a) :
    ∃ k : Fin n -> Fin (d + 1) -> ℂ,
      BHW.sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (BHW.sourceComplexGramDifferential d n (BHW.realEmbed x) k) = A
```

With this theorem in hand, the hard range theorem is immediate:
given `δ = sourceComplexGramDifferential d n z hz`, prove the selected target is
symmetric using `sourceComplexGramDifferential_symm`, choose `kx` whose selected
differential coordinates match those of `δ`, then apply the selected
cross-differential equality theorem.

This whole tangent packet is now checked in
`BHWPermutation/SourceComplexTangent.lean`, including
`sourceComplexGramTangent_subset_realEmbed_range_of_regular` and
`sourceComplexifiedRealTangentEqualsComplexTangent_of_regular`.  The final
comparison proof is the two span inclusions above: the `≤` direction is the
easy complexification inclusion; for `≥`, generators of the complex tangent
span lie in the real-embedded range by the hard theorem, and that range lies in
the complexified real-tangent span by the second inclusion.

**C. Hall-Wightman uniqueness from a real environment.**

This is the source-backed SCV theorem.  It should be proved once, at the
scalar-product-variety level, and then reused by the OS supplier.  The proof is
Hall-Wightman's Section 2 real-environment argument plus the ordinary identity
theorem in local variety charts:

1. choose `G0 ∈ O` from `hO.nonempty`.  Because `O` is relatively open in the
   real Gram variety and every point of `O` is regular/maximal-totally-real, the
   selected-coordinate Hall-Wightman chart at a regular realizer of `G0` gives a
   complex local chart on `sourceComplexGramVariety d n` whose real slice is a
   genuine open set in `ℝ^N`;
2. shrink that chart inside the given relatively open complex domain `U` using
   `hO_sub`, and restrict `(Φ - Ψ)` to the selected-coordinate chart;
3. apply the ordinary totally-real identity theorem in the selected complex
   coordinates to obtain a nonempty relatively open complex subpatch
   `W ⊆ U` on which `Φ = Ψ`;
4. propagate equality from `W` to all of connected `U` by the
   Hall-Wightman/Bochner-Martin analytic-continuation theorem for the irreducible
   scalar-product variety.  This is not the elementary full-matrix clopen
   argument: a connected reducible analytic set can carry a holomorphic function
   that vanishes on a relatively open subset of one component only.  The source
   Gram variety is irreducible because it is the Zariski closure/image of the
   polynomial Gram map, and this irreducibility is the genuine source input.

Therefore the Lean-facing theorem packet below has two real mathematical
lemmas.  The first is the local selected-coordinate totally-real chart theorem;
the second is the irreducible-variety identity-continuation theorem.  Neither
should be replaced by the already checked full-matrix identity theorem
`sourceDistributionalUniquenessSet_of_isOpen_nonempty`, which applies only when
the real environment contains an open subset of the whole matrix space.

Local source audit: `references/hall_wightman_invariant_analytic_functions_1957.pdf`
states in its synopsis and introduction that invariant analytic functions are
analytic functions of scalar products, that these functions live on the complex
scalar-product variety when the scalar-product image is not full-dimensional,
and that values on suitable real space-like subdomains uniquely determine the
function.  Its proof outline explicitly distinguishes regular scalar-product
points, where local neighborhoods are analytic-coordinate neighborhoods in the
tangent/selected scalar-product coordinates, from singular lower-rank points
where a Bochner-Martin analytic-variety notion is needed.  This is exactly the
source content represented by the two theorem surfaces below.

Lean-facing theorem packet:

The implementation should use the zero-function forms below.  Pairwise
`Φ`/`Ψ` statements are readable in prose, but implementing both pair and zero
versions would create wrappers.  The only pairwise theorem that should remain
public is the existing consumer predicate
`sourceDistributionalUniquenessSetOnVariety`; its proof sets `H := Φ - Ψ` and
uses the zero-function source theorems directly.

```lean
theorem BHW.SourceVarietyHolomorphicOn.sub
    (d n : ℕ)
    {U : Set (Fin n -> Fin n -> ℂ)}
    {Φ Ψ : (Fin n -> Fin n -> ℂ) -> ℂ}
    (hΦ : BHW.SourceVarietyHolomorphicOn d n Φ U)
    (hΨ : BHW.SourceVarietyHolomorphicOn d n Ψ U) :
    BHW.SourceVarietyHolomorphicOn d n (fun Z => Φ Z - Ψ Z) U
```

Proof transcript for `SourceVarietyHolomorphicOn.sub`: for each `Z ∈ U`,
choose ambient open neighborhoods `UΦ`, `UΨ` from `hΦ` and `hΨ`; use
`U0 = UΦ ∩ UΨ`; holomorphicity is `hDiffΦ.mono ...` sub
`hDiffΨ.mono ...`; the local variety-subset condition is inherited from either
side.  This is analytic bookkeeping and should live next to the existing
`of_subset_relOpen` and `precomp_sourcePermuteComplexGram` lemmas.

Complex selected-coordinate chart substrate:

```lean
theorem BHW.contDiff_sourceMinkowskiGram
    (d n : ℕ) :
    ContDiff ℂ ⊤ (BHW.sourceMinkowskiGram d n)

theorem BHW.sourceMinkowskiGram_hasFDerivAt
    (d n : ℕ)
    (z : Fin n -> Fin (d + 1) -> ℂ) :
    HasFDerivAt (BHW.sourceMinkowskiGram d n)
      (LinearMap.toContinuousLinearMap
        (BHW.sourceComplexGramDifferential d n z)) z

def BHW.sourceSelectedComplexSymCoordSubspace
    (n m : ℕ) (I : Fin m -> Fin n) :
    Submodule ℂ (Fin n -> Fin m -> ℂ)

def BHW.sourceSelectedComplexGramDifferentialToSym
    (d n m : ℕ)
    (z : Fin n -> Fin (d + 1) -> ℂ)
    (I : Fin m -> Fin n) :
    (Fin n -> Fin (d + 1) -> ℂ) →ₗ[ℂ]
      BHW.sourceSelectedComplexSymCoordSubspace n m I

def BHW.sourceSelectedComplexGramMap
    (d n m : ℕ)
    (I : Fin m -> Fin n) :
    (Fin n -> Fin (d + 1) -> ℂ) ->
      BHW.sourceSelectedComplexSymCoordSubspace n m I

theorem BHW.sourceSelectedComplexGramMap_hasStrictFDerivAt
    (d n m : ℕ)
    (I : Fin m -> Fin n)
    (z : Fin n -> Fin (d + 1) -> ℂ) :
    HasStrictFDerivAt
      (BHW.sourceSelectedComplexGramMap d n m I)
      (LinearMap.toContinuousLinearMap
        (BHW.sourceSelectedComplexGramDifferentialToSym d n m z I)) z

theorem BHW.sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x ≠ 0) :
    Function.Surjective
      (BHW.sourceSelectedComplexGramDifferentialToSym d n
        (min n (d + 1)) (BHW.realEmbed x) I)

theorem BHW.sourceSelectedComplexGramMap_implicit_chart_of_nonzero_minor
    (d n : ℕ)
    {x0 : Fin n -> Fin (d + 1) -> ℝ}
    {I : Fin (min n (d + 1)) -> Fin n}
    {J : Fin (min n (d + 1)) -> Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : BHW.sourceRegularMinor d n I J x0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (Fin n -> Fin (d + 1) -> ℂ)
        (BHW.sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
          LinearMap.ker
            (BHW.sourceSelectedComplexGramDifferentialToSym d n
              (min n (d + 1)) (BHW.realEmbed x0) I)),
      BHW.realEmbed x0 ∈ e.source ∧
      e (BHW.realEmbed x0) =
        (BHW.sourceSelectedComplexGramMap d n (min n (d + 1)) I
          (BHW.realEmbed x0), 0) ∧
      ∀ z ∈ e.source,
        (e z).1 =
          BHW.sourceSelectedComplexGramMap d n (min n (d + 1)) I z
```

Proof transcript for the complex chart substrate:

1. `sourceSelectedComplexSymCoordSubspace` is the complex analogue of
   `sourceSelectedSymCoordSubspace`: its carrier is
   `{A | ∀ a b, A (I a) b = A (I b) a}`.
2. `sourceSelectedComplexGramDifferentialToSym` restricts
   `sourceSelectedComplexGramCoord n m I ∘ sourceComplexGramDifferential d n z`
   to that subspace, using `sourceComplexGramDifferential_symm`.
3. `sourceSelectedComplexGramMap` restricts
   `sourceSelectedComplexGramCoord n m I (sourceMinkowskiGram d n z)` to the
   same subspace, using `sourceMinkowskiGram_symm`.
4. The strict derivative proof is the complex copy of the checked real theorem
   `sourceSelectedRealGramMap_hasStrictFDerivAt`: prove complex smoothness of
   `sourceMinkowskiGram d n` coordinatewise as a finite sum of quadratic complex
   coordinate monomials, identify its derivative with
   `sourceComplexGramDifferential d n z`, compose with the selected-coordinate
   continuous linear map, and coerce to the restricted codomain by
   `HasStrictFDerivAt.of_isLittleO`.
5. Surjectivity at `realEmbed x0` is exactly the checked theorem
   `sourceSelectedComplexGramDifferential_surjective_of_sourceRegularMinor_ne_zero`
   from `SourceComplexTangent.lean`; apply `implicitToOpenPartialHomeomorph` as
   in the real proof.  No dual-basis or rank theorem should be reproved here.

This full complex local-IFT substrate is now checked in
`BHWPermutation/SourceComplexChart.lean`:

```lean
BHW.contDiff_sourceMinkowskiGram
BHW.sourceMinkowskiGram_hasFDerivAt
BHW.sourceSelectedComplexSymCoordSubspace
BHW.mem_sourceSelectedComplexSymCoordSubspace
BHW.sourceSelectedComplexGramCoord_differential_mem
BHW.sourceSelectedComplexGramDifferentialToSym
BHW.sourceSelectedComplexGramDifferentialToSym_apply
BHW.sourceSelectedComplexGramMap
BHW.sourceSelectedComplexGramMap_apply
BHW.sourceSelectedComplexGramMap_hasStrictFDerivAt
BHW.sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
BHW.sourceSelectedComplexGramMap_implicit_chart_of_nonzero_minor
```

This slice reuses the checked selected-surjectivity theorem from
`SourceComplexTangent.lean` and does not reopen the selected-row rank proof.

The target of this selected chart is the selected-symmetric subspace, not the
full product `Fin n -> Fin m -> ℂ`.  Before applying the existing flat
`SCV.identity_theorem_totally_real`, the implementation needs an explicit
coordinate equivalence from that subspace to `Fin N -> ℂ`, with a matching real
equivalence to `Fin N -> ℝ`.  This is not a wrapper: it is the
finite-dimensional coordinate model that makes "maximal totally real" visible
to Lean.

```lean
def BHW.sourceSelectedSymCoordKey
    (n m : ℕ) (I : Fin m -> Fin n) : Type :=
  {q : Fin n × Fin m //
    ∀ c : Fin m, q.1.1 = I c -> q.1.2.val ≤ c.val}

noncomputable def BHW.sourceSelectedComplexSymCoordKeyEquiv
    (n m : ℕ) {I : Fin m -> Fin n}
    (hI : Function.Injective I) :
    BHW.sourceSelectedComplexSymCoordSubspace n m I ≃L[ℂ]
      (BHW.sourceSelectedSymCoordKey n m I -> ℂ)

noncomputable def BHW.sourceSelectedRealSymCoordKeyEquiv
    (n m : ℕ) {I : Fin m -> Fin n}
    (hI : Function.Injective I) :
    BHW.sourceSelectedSymCoordSubspace n m I ≃L[ℝ]
      (BHW.sourceSelectedSymCoordKey n m I -> ℝ)

def BHW.sourceSelectedSymCoordRealComplexify
    (n m : ℕ) (I : Fin m -> Fin n) :
    BHW.sourceSelectedSymCoordSubspace n m I ->ₗ[ℝ]
      BHW.sourceSelectedComplexSymCoordSubspace n m I

theorem BHW.sourceSelectedComplexSymCoordKeyEquiv_real_slice
    (n m : ℕ) {I : Fin m -> Fin n}
    (hI : Function.Injective I)
    (A : BHW.sourceSelectedSymCoordSubspace n m I) :
    BHW.sourceSelectedComplexSymCoordKeyEquiv n m hI
      (BHW.sourceSelectedSymCoordRealComplexify n m I A) =
      fun q => (BHW.sourceSelectedRealSymCoordKeyEquiv n m hI A q : ℂ)

noncomputable def BHW.sourceSelectedComplexSymCoordFinEquiv
    (n m : ℕ) {I : Fin m -> Fin n}
    (hI : Function.Injective I) :
    BHW.sourceSelectedComplexSymCoordSubspace n m I ≃L[ℂ]
      (Fin (Fintype.card (BHW.sourceSelectedSymCoordKey n m I)) -> ℂ)

noncomputable def BHW.sourceSelectedRealSymCoordFinEquiv
    (n m : ℕ) {I : Fin m -> Fin n}
    (hI : Function.Injective I) :
    BHW.sourceSelectedSymCoordSubspace n m I ≃L[ℝ]
      (Fin (Fintype.card (BHW.sourceSelectedSymCoordKey n m I)) -> ℝ)

theorem BHW.sourceSelectedComplexSymCoordFinEquiv_real_slice
    (n m : ℕ) {I : Fin m -> Fin n}
    (hI : Function.Injective I)
    (A : BHW.sourceSelectedSymCoordSubspace n m I) :
    BHW.sourceSelectedComplexSymCoordFinEquiv n m hI
      (BHW.sourceSelectedSymCoordRealComplexify n m I A) =
      SCV.realToComplex
        (BHW.sourceSelectedRealSymCoordFinEquiv n m hI A)
```

Here `sourceSelectedSymCoordRealComplexify` is the componentwise complexification
from the real selected-symmetric subspace to the complex one.  The proof of the
key equivalence is explicit.  Use `Equiv.ofInjective I hI` to recognize selected
rows, and do not use cardinal arithmetic or abstract finite-dimensional
dimension equality for the equivalence itself.

1. keep every coordinate `(i,a)` whose row `i` is not a selected row;
2. on a selected row `i = I c`, keep the lower-triangular selected-block
   coordinate `a ≤ c`;
3. reconstruct a dropped upper-triangular selected-block coordinate by the
   symmetry relation `A (I c) a = A (I a) c`;
4. use `hI` for uniqueness of the selected-row index;
5. compose with `Fintype.equivFin (sourceSelectedSymCoordKey n m I)` and
   `LinearEquiv.piCongrLeft` to get the flat `Fin N -> ℂ` and `Fin N -> ℝ`
   coordinate equivalences used by `SCV.identity_theorem_totally_real`.

Implementation transcript for the key equivalence:

```lean
private noncomputable def BHW.sourceSelectedComplexSymCoordKeyEvalCLM
    (n m : ℕ) (I : Fin m -> Fin n) :
    BHW.sourceSelectedComplexSymCoordSubspace n m I ->L[ℂ]
      (BHW.sourceSelectedSymCoordKey n m I -> ℂ)

private noncomputable def BHW.sourceSelectedRealSymCoordKeyEvalCLM
    (n m : ℕ) (I : Fin m -> Fin n) :
    BHW.sourceSelectedSymCoordSubspace n m I ->L[ℝ]
      (BHW.sourceSelectedSymCoordKey n m I -> ℝ)

private noncomputable def BHW.sourceSelectedSymCoordKeyReconstructScalar
    (n m : ℕ) {I : Fin m -> Fin n}
    (hI : Function.Injective I)
    (𝕜 : Type*) [Zero 𝕜]
    (f : BHW.sourceSelectedSymCoordKey n m I -> 𝕜) :
    Fin n -> Fin m -> 𝕜 :=
  fun i a =>
    if hi : i ∈ Set.range I then
      let c := (Equiv.ofInjective I hI).symm ⟨i, hi⟩
      if hle : a.val ≤ c.val then
        f ⟨(i, a), by
          intro c' hic'
          have hc' : c' = c := by
            apply hI
            rw [← hic']
            exact ((Equiv.ofInjective I hI).apply_symm_apply ⟨i, hi⟩).symm
          simpa [hc'] using hle⟩
      else
        f ⟨(I a, c), by
          intro b hb
          have hb' : b = a := hI hb.symm
          have hlt : c.val < a.val := Nat.lt_of_not_ge hle
          simpa [hb'] using le_of_lt hlt⟩
    else
      f ⟨(i, a), by
        intro c hic
        exact False.elim (hi ⟨c, hic.symm⟩)⟩

private theorem BHW.sourceSelectedSymCoordKeyReconstruct_mem_complex
    ... :
    BHW.sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ f ∈
      BHW.sourceSelectedComplexSymCoordSubspace n m I

private theorem BHW.sourceSelectedSymCoordKeyReconstruct_mem_real
    ... :
    BHW.sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ f ∈
      BHW.sourceSelectedSymCoordSubspace n m I

private theorem BHW.sourceSelectedComplexSymCoordKeyEval_reconstruct
    ... :
    BHW.sourceSelectedComplexSymCoordKeyEvalCLM n m I
      ⟨BHW.sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ f,
        BHW.sourceSelectedSymCoordKeyReconstruct_mem_complex ...⟩ = f

private theorem BHW.sourceSelectedComplexSymCoordKeyReconstruct_eval
    ... :
    ⟨BHW.sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ
        (BHW.sourceSelectedComplexSymCoordKeyEvalCLM n m I A),
      BHW.sourceSelectedSymCoordKeyReconstruct_mem_complex ...⟩ = A
```

There are identical real versions of the two inverse theorems, replacing
`ℂ` and `sourceSelectedComplexSymCoordKeyEvalCLM` by `ℝ` and
`sourceSelectedRealSymCoordKeyEvalCLM`.  The `*_mem_*` proof splits
`lt_trichotomy a c` for
`A (I c) a = A (I a) c`.  If `a ≤ c`, both sides evaluate the kept lower
coordinate.  If `c < a`, both sides evaluate the kept coordinate `(I a,c)`.
The diagonal case is reflexive.  The two inverse proofs are coordinate
extensionality:

* for `eval_reconstruct`, split on whether the key row is selected.  If it is
  not selected, the reconstruction uses the same key directly.  If it is
  selected, the key condition forces the lower-triangular branch, and subtype
  extensionality identifies the key;
* for `reconstruct_eval`, split on whether the row is selected and then on
  `a.val ≤ c.val`.  The lower branch is direct; the upper branch is exactly the
  selected-symmetry relation in the subspace.

The continuous linear equivalence is then built by
`ContinuousLinearEquiv.equivOfInverse` from the checked evaluation and
reconstruction continuous linear maps.  The flat `Fin N` versions are

```lean
(BHW.sourceSelectedComplexSymCoordKeyEquiv n m hI).trans
  (ContinuousLinearEquiv.piCongrLeft ℂ
      (fun _ : Fin (Fintype.card
        (BHW.sourceSelectedSymCoordKey n m I)) => ℂ)
      (Fintype.equivFin (BHW.sourceSelectedSymCoordKey n m I)))
```

and similarly over `ℝ`.  The real-slice theorem is `ext q; rfl` before the
`Fintype.equivFin` reindexing and then `ext k` after reindexing.

This selected-symmetric coordinate bridge is now checked in
`BHWPermutation/SourceComplexChart.lean`:

```lean
BHW.sourceSelectedSymCoordKey
BHW.sourceSelectedSymCoordKey.fintype
BHW.sourceSelectedComplexSymCoordKeyEvalCLM
BHW.sourceSelectedRealSymCoordKeyEvalCLM
BHW.sourceSelectedSymCoordRealComplexify
BHW.sourceSelectedSymCoordRealComplexify_apply
BHW.sourceSelectedComplexSymCoordKeyEvalCLM_real_slice
BHW.sourceSelectedComplexSymCoordKeyEquiv
BHW.sourceSelectedRealSymCoordKeyEquiv
BHW.sourceSelectedComplexSymCoordKeyEquiv_real_slice
BHW.sourceSelectedComplexSymCoordFinEquiv
BHW.sourceSelectedRealSymCoordFinEquiv
BHW.sourceSelectedComplexSymCoordFinEquiv_real_slice
```

The local selected-coordinate variety chart needed by the zero theorem is a
slightly stronger package than the bare complex implicit-function chart above:
it must produce a scalar-product-variety coordinate chart whose real slice is
compatible with the checked real selected-coordinate chart.  The theorem shape
should be:

```lean
theorem BHW.sourceComplexGramVariety_selectedChart_of_realRegular
    (d n : ℕ)
    {x0 : Fin n -> Fin (d + 1) -> ℝ}
    (hreg : BHW.SourceGramRegularAt d n x0)
    {V : Set (Fin n -> Fin (d + 1) -> ℂ)}
    (hV_open : IsOpen V)
    (hx0V : BHW.realEmbed x0 ∈ V) :
    ∃ (N : ℕ)
      (D : Set (Fin N -> ℂ))
      (Vre : Set (Fin N -> ℝ))
      (Γ : (Fin N -> ℂ) -> (Fin n -> Fin n -> ℂ))
      (γre : (Fin N -> ℝ) -> (Fin n -> Fin (d + 1) -> ℝ)),
      IsOpen D ∧ IsConnected D ∧
      IsOpen Vre ∧ Vre.Nonempty ∧
      (∀ q ∈ Vre, SCV.realToComplex q ∈ D) ∧
      Γ '' D ⊆ BHW.sourceComplexGramVariety d n ∧
      Γ '' D ⊆ BHW.sourceMinkowskiGram d n '' V ∧
      BHW.IsRelOpenInSourceComplexGramVariety d n (Γ '' D) ∧
      (BHW.sourceRealGramComplexify n
        (BHW.sourceRealMinkowskiGram d n x0)) ∈ Γ '' D ∧
      (∀ z ∈ D, ∃ w ∈ V, Γ z = BHW.sourceMinkowskiGram d n w) ∧
      ContinuousOn γre Vre ∧
      (∃ q0 ∈ Vre, γre q0 = x0 ∧
        Γ (SCV.realToComplex q0) =
          BHW.sourceRealGramComplexify n
            (BHW.sourceRealMinkowskiGram d n x0)) ∧
      (∀ q ∈ Vre,
        BHW.SourceGramRegularAt d n (γre q) ∧
        BHW.sourceRealMinkowskiGram d n (γre q) ∈
          BHW.sourceRealGramVariety d n ∧
        Γ (SCV.realToComplex q) =
          BHW.sourceRealGramComplexify n
            (BHW.sourceRealMinkowskiGram d n (γre q))) ∧
      DifferentiableOn ℂ Γ D
```

The proof of this chart package follows the real local image theorem
`sourceRealGramMap_localRelOpenImage_in_open_of_regular`, but with the complex
selected chart:

1. choose a nonzero selected minor `I,J` for `x0`;
2. build the complex selected implicit chart and shrink its source by the
   nonzero complex minor and the prescribed open set `V`;
3. use vertical constancy of the full complex Gram map on selected-coordinate
   fibers, now checked as
   `sourceComplexGramMap_constant_on_selectedVerticalFibers`;
4. define `Γ q` as the full complex Gram matrix of the zero-kernel section of
   the complex selected chart;
5. prove relative openness of `Γ '' D` exactly as in the real proof: the open
   image of the implicit chart is projected to the selected-coordinate subspace,
   transported through `sourceSelectedComplexSymCoordFinEquiv`, then pulled back
   by the selected-coordinate projection on full Gram matrices;
6. define `γre q` as the real zero-kernel section of the real selected chart in
   the same flat coordinates; prove `ContinuousOn γre Vre`, `γre q0 = x0` at
   the base coordinate, and
   `Γ (SCV.realToComplex q) =
    sourceRealGramComplexify n (sourceRealMinkowskiGram d n (γre q))`;
7. prove real-slice compatibility by choosing the complex chart to be the
   complexification of the real selected chart, or, equivalently, by proving
   the zero-kernel section commutes with componentwise conjugation and hence
   sends real selected coordinates to real source points.  This is a necessary
   Lean obligation; without it `h_zero` on the real environment cannot be
   transported to the coordinate slice;
8. differentiability of `Γ` follows from its construction as the Gram map
   composed with the holomorphic zero-kernel section of the selected implicit
   chart.  In `sourceVariety_localChart_totallyReal_zero`, holomorphicity of
   `H ∘ Γ` is then proved pointwise from `SourceVarietyHolomorphicOn`: for each
   `z ∈ D`, choose an ambient open representative neighborhood of `H` around
   `Γ z`; continuity of `Γ` shrinks a neighborhood of `z` into it, and the local
   composition rule gives `DifferentiableWithinAt` on `D`.

The local totally-real theorem should then be implemented in zero form:

```lean
theorem BHW.sourceVariety_localChart_totallyReal_zero
    (d n : ℕ)
    {O : Set (Fin n -> Fin n -> ℝ)}
    (hO : BHW.IsHWRealEnvironment d n O)
    {U : Set (Fin n -> Fin n -> ℂ)}
    {H : (Fin n -> Fin n -> ℂ) -> ℂ}
    (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
    (hO_sub : ∀ G ∈ O, BHW.sourceRealGramComplexify n G ∈ U)
    (hH : BHW.SourceVarietyHolomorphicOn d n H U)
    (h_zero : ∀ G ∈ O, H (BHW.sourceRealGramComplexify n G) = 0) :
    ∃ W : Set (Fin n -> Fin n -> ℂ),
      BHW.IsRelOpenInSourceComplexGramVariety d n W ∧
      W.Nonempty ∧ W ⊆ U ∧ Set.EqOn H 0 W
```

Proof transcript for `sourceVariety_localChart_totallyReal_zero`:

1. choose `G0 ∈ O` and a Jost regular realizer
   `x0` from `hO.realized_by_jost G0`;
2. choose a nonzero selected minor `I,J` for `x0`;
3. write `hU_rel` as `U = U0 ∩ sourceComplexGramVariety d n`, with `U0` open.
   Since `sourceRealGramComplexify n G0 ∈ U`, the source preimage
   `{z | sourceMinkowskiGram d n z ∈ U0}` is an open neighborhood of
   `realEmbed x0`;
4. use `hO.relOpen` to write `O = O0 ∩ sourceRealGramVariety d n`, with
   `O0` open.  Shrink the real source neighborhood by
   `{y | sourceRealMinkowskiGram d n y ∈ O0}` and the complex source
   neighborhood by `{z | sourceMinkowskiGram d n z ∈ U0}`;
5. apply
   `sourceComplexGramVariety_selectedChart_of_realRegular` at `x0` inside the
   shrunken complex source neighborhood.  The chart gives flat coordinates
   `D : Set (Fin N -> ℂ)`, a real slice `Vre : Set (Fin N -> ℝ)`, and
   `Γ : (Fin N -> ℂ) -> (Fin n -> Fin n -> ℂ)` with `Γ '' D ⊆ U`;
6. refine the real slice by intersecting `Vre` with the open condition that its
   real source realizer has Gram in `O0`.  Nonemptiness is preserved at the base
   coordinate, and every real-slice point then gives a Gram matrix in `O`, so
   `h_zero` gives
   `H (Γ (SCV.realToComplex q)) = 0`;
7. define the coordinate pullback `hcoord z := H (Γ z)`.  Its holomorphicity on
   `D` follows from `SourceVarietyHolomorphicOn`, the inclusion `Γ '' D ⊆ U`,
   and the chart output `DifferentiableOn ℂ Γ D`, as described in the chart
   transcript above;
8. apply the flat theorem `SCV.identity_theorem_totally_real` to `hcoord`,
   the connected open coordinate domain `D`, and the nonempty open real slice
   from step 6;
9. push the resulting zero set back through the chart to obtain the required
   nonempty relatively open `W`.

The complex selected-minor algebra and the scalar-variety relative-open image
half of this chart are now checked in `BHWPermutation/SourceComplexChart.lean`:

```lean
BHW.sourceComplexRegularMinor
BHW.continuous_sourceComplexRegularMinor
BHW.sourceComplexRegularMinor_realEmbed
BHW.linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
BHW.span_sourceComplexRows_eq_sourceComplexConfigurationSpan_of_sourceComplexRegularMinor_ne_zero
BHW.sourceSelectedComplexRows_span_top_of_sourceComplexRegularMinor_ne_zero
BHW.sourceComplexStdBasis_sum
BHW.sourceComplexMinkowskiDualVectorOfLinearFunctional
BHW.sourceComplexMinkowskiInner_dualVectorOfLinearFunctional
BHW.exists_sourceComplexMinkowski_dual_family_of_linearIndependent
BHW.exists_sourceComplexMinkowski_dual_sourceRows_of_sourceComplexRegularMinor_ne_zero
BHW.sourceComplexMinkowskiInner_sum_smul_dual_left
BHW.sourceSelectedComplexGramCoord_comp_differential_range_eq_of_sourceComplexRegularMinor_ne_zero
BHW.sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero
BHW.sourceComplexRows_coefficients_of_sourceComplexRegularMinor_ne_zero
BHW.sourceSelectedComplexGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop
BHW.sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero
BHW.sourceComplexGramMap_constant_on_selectedVerticalFibers
BHW.sourceSelectedComplexRows_span_top_of_selectedComplexGramCoord_eq_regular
BHW.sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety
BHW.sourceComplexGramMap_localRelOpenImage_in_open_of_realRegular
```

The remaining work in `sourceComplexGramVariety_selectedChart_of_realRegular`
is therefore no longer the selected-minor algebra, the relative-open image
packet, or the finite-dimensional IFT differentiability packet.  Those pieces
are checked in `BHWPermutation/SourceComplexChart.lean` and
`BHWPermutation/SourceComplexZeroSection.lean`:

```lean
BHW.contDiff_sourceSelectedComplexGramMap_of_injective
BHW.sourceSelectedComplexGramKernelProjection
BHW.sourceSelectedComplexGramKernelProjection_apply_ker
BHW.sourceSelectedComplexGramProdMap
BHW.contDiff_sourceSelectedComplexGramProdMap
BHW.sourceSelectedComplexGramProdMap_hasFDerivAt
BHW.sourceSelectedComplexGramProdMap_fderiv
BHW.sourceSelectedComplexGramProdMap_base_fderiv_isInvertible
BHW.sourceSelectedComplexGramProdMap_local_invertible_nhds
BHW.sourceSelectedComplexGramImplicitChart
BHW.sourceSelectedComplexGramImplicitChart_apply
BHW.sourceSelectedComplexGramImplicitChart_mem_source
BHW.sourceSelectedComplexGramImplicitChart_self
BHW.sourceSelectedComplexZeroKernelTargetCLM
BHW.sourceSelectedComplexZeroKernelTargetCLM_apply
BHW.sourceSelectedComplexGramZeroSection_differentiableOn
BHW.sourceSelectedComplexGramZeroSection_selectedGram
BHW.sourceSelectedComplexGramZeroSection_base
BHW.sourceSelectedComplexGramFlatCoordCLM
BHW.sourceSelectedComplexGramFlatCoordCLM_apply
BHW.sourceSelectedComplexGramFlatCoordCLM_source
BHW.sourceSelectedComplexGramCoord_eq_of_flatCoord_eq
BHW.sourceSelectedComplexGramZeroSection_image_eq_flatCoord_preimage
BHW.sourceSelectedComplexGramZeroSection_image_relOpen
BHW.sourceSelectedComplexGramZeroSection_gram_differentiableOn
BHW.exists_sourceSelectedComplexGramZeroSection_good_ball
BHW.sourceSelectedComplexSymCoordFinEquiv_symm_real_slice
BHW.sourceSelectedRealGramImplicitChart
BHW.sourceSelectedRealGramImplicitChart_mem_source
BHW.sourceSelectedRealGramImplicitChart_self
BHW.sourceSelectedRealGramImplicitChart_fst
BHW.sourceSelectedRealZeroKernelTargetCLM
BHW.sourceSelectedRealZeroKernelTargetCLM_apply
BHW.sourceSelectedRealGramZeroSection_selectedGram
BHW.sourceSelectedRealGramZeroSection_base
BHW.sourceSelectedRealGramZeroSection_continuousOn
BHW.sourceSelectedComplexGramZeroSection_real_slice_gram
BHW.exists_sourceSelectedRealGramZeroSection_good_ball
BHW.sourceSelectedComplexGramBaseCoord_real_slice
BHW.sourceComplexGramVariety_selectedChart_of_realRegular
BHW.SourceVarietyHolomorphicOn.comp_differentiableOn_chart
BHW.sourceVariety_localChart_totallyReal_zero
```

The proof of the chart theorem should now be a local shrink and packaging
argument:

1. choose a nonzero selected minor `I,J` for the regular real source point
   `x0`;
2. form the checked complex chart `eC` and real chart `eR` for this same minor;
3. use `sourceSelectedComplexGramProdMap_local_invertible_nhds` to choose a
   complex source neighborhood on which the derivative of the product map is
   invertible, contained in the prescribed source neighborhood `V` and in the
   nonzero complex-minor patch;
4. the complex flat coordinate ball `D` is now supplied by the checked theorem
   `exists_sourceSelectedComplexGramZeroSection_good_ball`.  It uses openness
   of `eC.target`, continuity of `eC.symm` at the base target, continuity of
   the zero-kernel target map, and the checked derivative-invertibility source
   shrink; the resulting `D` is a metric ball, hence open and connected;
5. the matching flat real coordinate ball `Vre` is now supplied by the checked
   theorem `exists_sourceSelectedRealGramZeroSection_good_ball`, in
   `BHWPermutation/SourceComplexLocalChart.lean`.  It ensures
   `SCV.realToComplex '' Vre ⊆ D`, every real zero-kernel target lies in
   `eR.target`, the inverse real source remains in the nonzero real-minor patch,
   and the real source is regular;
6. define `Γ q` as the full complex Gram matrix of the complex zero-section and
   `γre q` as the real zero-section source.  The checked
   `sourceSelectedComplexGramZeroSection_gram_differentiableOn` proves
   `DifferentiableOn ℂ Γ D`, and the checked
   `sourceSelectedRealGramZeroSection_continuousOn` proves
   `ContinuousOn γre Vre`;
7. relative openness of `Γ '' D` is now checked by
   `sourceSelectedComplexGramZeroSection_image_relOpen`.  Its stronger image
   equation
   `sourceSelectedComplexGramZeroSection_image_eq_flatCoord_preimage` proves
   that every variety point with selected coordinates in the flat ball is the
   full Gram matrix of the zero-kernel section, not merely that it has some
   source realization;
8. prove the real-slice equation from the checked theorem
   `sourceSelectedComplexGramZeroSection_real_slice_gram`.  The selected
   coordinate equations are now exposed by
   `sourceSelectedComplexGramZeroSection_selectedGram` and
   `sourceSelectedRealGramZeroSection_selectedGram`; the base coordinate maps
   back to `x0` by `sourceSelectedComplexGramZeroSection_base` and
   `sourceSelectedRealGramZeroSection_base`, so the real ball is nonempty
   because it contains this base coordinate.

The final local chart assembly is now checked as
`sourceComplexGramVariety_selectedChart_of_realRegular`, in
`BHWPermutation/SourceComplexLocalChart.lean`.  The proof uses the base
real-slice equality `sourceSelectedComplexGramBaseCoord_real_slice` to feed the
real ball theorem from the complex ball base membership, then assembles the
checked differentiability, relative-openness, image, base-point, regularity,
and real-slice lemmas.  No Hall-Wightman branch law or theorem-2-specific
identity principle is hidden in this local chart packet.

The local zero theorem is now checked as
`sourceVariety_localChart_totallyReal_zero`: it uses the checked local chart at
a regular real environment point, pulls a variety-holomorphic scalar
representative back to flat coordinates using
`SourceVarietyHolomorphicOn.comp_differentiableOn_chart`, applies the flat
totally-real identity theorem on the connected complex coordinate ball and
nonempty open real slice, and pushes the zero set back to a nonempty relatively
open subset of the original variety domain.

The remaining theorem-2 source uniqueness target is the global continuation
from that nonempty relatively open zero set to the whole connected relatively
open source Gram domain:
`sourceComplexGramVariety_identity_principle`.

The complex selected-coordinate chart theorem itself should be proved from the
same algebra now checked in `SourceComplexTangent.lean`: selected-row spanning,
shared coefficient expansion, selected-coordinate uniqueness, and the complex
implicit-function theorem for the selected Gram map.  It is genuine BHW geometry,
not a wrapper.  The real-slice compatibility in
`sourceComplexGramVariety_selectedChart_of_realRegular` is a hard requirement:
without it, the theorem would only produce complex source points over real
selected coordinates, and the hypothesis `h_zero` on the Hall-Wightman real
environment would not apply.

The real-slice compatibility is now reduced to a checked pointwise Gram theorem:
`sourceSelectedComplexGramZeroSection_real_slice_gram`.  Its proof does not
claim that the complex zero-section source point is literally the real
embedding of the real zero-section source point.  Instead, it uses the inverse
flat-coordinate real-slice lemma
`sourceSelectedComplexSymCoordFinEquiv_symm_real_slice`, the first-component
equations for the complex and real implicit charts, and the checked selected
coordinate uniqueness theorem
`sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety`.
The needed remaining hypotheses for the chart construction are therefore
geometric shrink conditions: the real zero-section target lies in the real
chart target, the complex zero-section target lies in the complex chart target,
and the real zero-section source stays in the same nonzero real minor patch.

```lean

theorem BHW.sourceComplexGramVariety_identity_principle
    (d n : ℕ)
    {U W : Set (Fin n -> Fin n -> ℂ)}
    {H : (Fin n -> Fin n -> ℂ) -> ℂ}
    (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
    (hU_conn : IsConnected U)
    (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : BHW.SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 U
```

Proof transcript for `sourceComplexGramVariety_identity_principle`:

1. reduce the complex Minkowski form to the standard complex symmetric dot form.
   Since every metric-signature coefficient is `±1`, the coordinatewise complex
   scaling by `1` or `Complex.I` gives a complex-linear equivalence `L_d` with

   ```lean
   BHW.sourceComplexMinkowskiInner d u v =
     ∑ μ, (L_d u μ) * (L_d v μ)
   ```

   This proves that the source Gram image for the Minkowski form is linearly
   equivalent to the ordinary complex symmetric Gram image.  This stage is now
   checked in `BHWPermutation/SourceComplexGlobalIdentity.lean` as
   `complexMinkowskiToDotLinearEquiv`,
   `sourceComplexMinkowskiInner_eq_dot_after_equiv`,
   `sourceMinkowskiGram_eq_dotGram_after_equiv`, and
   `sourceComplexGramVariety_eq_dotGram_range`;
2. prove the algebraic source identification
   `sourceComplexGramVariety d n = sourceSymmetricRankLEVariety n (d + 1)`.
   The forward inclusion is symmetry plus rank at most `d + 1` for a Gram
   factorization.  The reverse inclusion is the complex symmetric factorization
   theorem: every complex symmetric `n × n` matrix of rank at most `D` can be
   written as `A * Aᵀ` with `A : Fin n -> Fin D -> ℂ`, then padded/transported
   through `L_d.symm`;
3. handle the easy case `n ≤ d + 1` separately.  Then the variety is the full
   symmetric matrix subspace.  This branch is now checked as
   `sourceComplexGramVariety_identity_principle_easy`: transport by the full
   selected symmetric-coordinate equivalence, apply the ordinary SCV identity
   theorem on the open connected coordinate domain, and reconstruct the
   symmetric matrix.  No rank singularity or determinantal irreducibility is
   needed in this case;
4. in the hard case `d + 1 < n`, prove analytic irreducibility of the symmetric
   rank-`≤ d+1` determinantal variety.  The proof route is the polynomial
   parametrization `A ↦ A * Aᵀ`, the factorization theorem from step 2, and the
   standard result that the analytic/Zariski closure of the polynomial image of
   an irreducible affine space is irreducible.  The statement must be
   analytic-variety-facing because `SourceVarietyHolomorphicOn` is an ambient
   holomorphic representative notion.  Do not model this as ordinary topological
   irreducibility of the Euclidean topology, which is the wrong notion for
   complex analytic varieties;
5. apply the analytic-set identity theorem: on an irreducible complex analytic
   set, an ambient-holomorphic function that vanishes on a nonempty relatively
   open subset of a connected relatively open domain vanishes on the whole
   domain;
6. instantiate that theorem with `H`, `U`, and `W`.

If this is not taken as one checked Hall-Wightman source theorem, the internal
Lean decomposition should expose the following pure finite-dimensional analytic
geometry facts, in this order:

```lean
def BHW.sourceComplexDotGram
    (D n : ℕ)
    (z : Fin n -> Fin D -> ℂ) :
    Fin n -> Fin n -> ℂ :=
  fun i j => ∑ μ : Fin D, z i μ * z j μ

def BHW.complexMinkowskiDotScale
    (d : ℕ) (μ : Fin (d + 1)) : ℂ :=
  if μ = 0 then Complex.I else 1

def BHW.complexMinkowskiDotInvScale
    (d : ℕ) (μ : Fin (d + 1)) : ℂ :=
  if μ = 0 then -Complex.I else 1

noncomputable def BHW.complexMinkowskiToDotLinearEquiv
    (d : ℕ) :
    (Fin (d + 1) -> ℂ) ≃ₗ[ℂ] (Fin (d + 1) -> ℂ)

theorem BHW.sourceComplexMinkowskiInner_eq_dot_after_equiv
    (d : ℕ) (u v : Fin (d + 1) -> ℂ) :
    BHW.sourceComplexMinkowskiInner d u v =
      ∑ μ : Fin (d + 1),
        BHW.complexMinkowskiToDotLinearEquiv d u μ *
          BHW.complexMinkowskiToDotLinearEquiv d v μ

theorem BHW.sourceMinkowskiGram_eq_dotGram_after_equiv
    (d n : ℕ)
    (z : Fin n -> Fin (d + 1) -> ℂ) :
    BHW.sourceMinkowskiGram d n z =
      BHW.sourceComplexDotGram (d + 1) n
        (fun i => BHW.complexMinkowskiToDotLinearEquiv d (z i))

theorem BHW.sourceComplexGramVariety_eq_dotGram_range
    (d n : ℕ) :
    BHW.sourceComplexGramVariety d n =
      Set.range (BHW.sourceComplexDotGram (d + 1) n)

def BHW.sourceSymmetricMatrixSpace
    (n : ℕ) : Set (Fin n -> Fin n -> ℂ) :=
  {Z | ∀ i j, Z i j = Z j i}

def BHW.sourceMatrixMinor
    (n k : ℕ)
    (I J : Fin k -> Fin n)
    (Z : Fin n -> Fin n -> ℂ) : ℂ :=
  Matrix.det (fun a b : Fin k => Z (I a) (J b))

def BHW.sourceSymmetricRankLEVariety
    (n D : ℕ) : Set (Fin n -> Fin n -> ℂ) :=
  if hD : D < n then
    {Z | (∀ i j, Z i j = Z j i) ∧
      ∀ I J : Fin (D + 1) -> Fin n,
        BHW.sourceMatrixMinor n (D + 1) I J Z = 0}
  else
    BHW.sourceSymmetricMatrixSpace n

theorem BHW.sourceComplexDotGram_symm
    (D n : ℕ)
    (z : Fin n -> Fin D -> ℂ)
    (i j : Fin n) :
    BHW.sourceComplexDotGram D n z i j =
      BHW.sourceComplexDotGram D n z j i

theorem BHW.sourceComplexDotGram_mem_sourceSymmetricMatrixSpace
    (D n : ℕ)
    (z : Fin n -> Fin D -> ℂ) :
    BHW.sourceComplexDotGram D n z ∈
      BHW.sourceSymmetricMatrixSpace n

theorem BHW.sourceComplexGramVariety_subset_sourceSymmetricMatrixSpace
    (d n : ℕ) :
    BHW.sourceComplexGramVariety d n ⊆
      BHW.sourceSymmetricMatrixSpace n

theorem BHW.sourceComplexDotGram_minor_eq_zero
    (D n : ℕ)
    (z : Fin n -> Fin D -> ℂ)
    (I J : Fin (D + 1) -> Fin n) :
    BHW.sourceMatrixMinor n (D + 1) I J
      (BHW.sourceComplexDotGram D n z) = 0

theorem BHW.sourceComplexDotGram_mem_sourceSymmetricRankLEVariety
    (D n : ℕ)
    (z : Fin n -> Fin D -> ℂ) :
    BHW.sourceComplexDotGram D n z ∈
      BHW.sourceSymmetricRankLEVariety n D

theorem BHW.sourceComplexGramVariety_subset_sourceSymmetricRankLEVariety
    (d n : ℕ) :
    BHW.sourceComplexGramVariety d n ⊆
      BHW.sourceSymmetricRankLEVariety n (d + 1)

noncomputable def BHW.complexSquareRootChoice (c : ℂ) : ℂ

theorem BHW.complexSquareRootChoice_mul_self (c : ℂ) :
    BHW.complexSquareRootChoice c *
      BHW.complexSquareRootChoice c = c

theorem BHW.sourceComplexDiagonal_factorization_self
    (n : ℕ) (w : Fin n -> ℂ) :
    ∃ A : Fin n -> Fin n -> ℂ,
      (fun i j => if i = j then w i else 0) =
        BHW.sourceComplexDotGram n n A

theorem BHW.complex_symmetric_matrix_factorization_rank_le
    (n D : ℕ)
    {Z : Fin n -> Fin n -> ℂ}
    (hZsym : ∀ i j, Z i j = Z j i)
    (hZrank : ∀ I J : Fin (D + 1) -> Fin n,
      BHW.sourceMatrixMinor n (D + 1) I J Z = 0) :
    ∃ A : Fin n -> Fin D -> ℂ,
      Z = fun i j => ∑ a : Fin D, A i a * A j a

theorem BHW.sourceComplexGramVariety_eq_rank_le
    (d n : ℕ) :
    BHW.sourceComplexGramVariety d n =
      {Z | Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
        (Matrix.of fun i j : Fin n => Z i j).rank ≤ d + 1}

theorem BHW.sourceSymmetricRankLEVariety_isAnalyticSet
    (n D : ℕ) :
    SCV.IsComplexAnalyticSet (BHW.sourceSymmetricRankLEVariety n D)

theorem BHW.sourceSymmetricRankLEVariety_analytic_irreducible
    (n D : ℕ) :
    SCV.AnalyticallyIrreducible
      (BHW.sourceSymmetricRankLEVariety n D)

theorem SCV.identity_theorem_analytically_irreducible
    {n : ℕ}
    {X U W : Set (Fin n -> Fin n -> ℂ)}
    {H : (Fin n -> Fin n -> ℂ) -> ℂ}
    (hX_irred : SCV.AnalyticallyIrreducible X)
    (hU_rel : ∃ U0, IsOpen U0 ∧ U = U0 ∩ X)
    (hU_conn : IsConnected U)
    (hW_rel : ∃ W0, IsOpen W0 ∧ W = W0 ∩ X)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : ∀ Z ∈ U, ∃ U0, IsOpen U0 ∧ Z ∈ U0 ∧
      DifferentiableOn ℂ H U0 ∧ U0 ∩ X ⊆ U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 U
```

Checked status of this decomposition:

1. `sourceComplexDotGram`, `complexMinkowskiDotScale`,
   `complexMinkowskiDotInvScale`, `complexMinkowskiToDotLinearEquiv`,
   `sourceComplexMinkowskiInner_eq_dot_after_equiv`,
   `sourceMinkowskiGram_eq_dotGram_after_equiv`, and
   `sourceComplexGramVariety_eq_dotGram_range` are production-checked and
   sorry-free.  The symmetric-space layer
   `sourceSymmetricMatrixSpace`, `sourceMatrixMinor`,
   `sourceSymmetricRankLEVariety`, `sourceComplexDotGram_symm`,
   `sourceComplexDotGram_mem_sourceSymmetricMatrixSpace`, and
   `sourceComplexGramVariety_subset_sourceSymmetricMatrixSpace` is also
   checked.  The determinant/rank forward inclusion is checked as
   `sourceComplexDotGram_minor_eq_zero`,
   `sourceComplexDotGram_mem_sourceSymmetricRankLEVariety`, and
   `sourceComplexGramVariety_subset_sourceSymmetricRankLEVariety`.  The
   diagonal square-root stage of the reverse factorization is checked as
   `complexSquareRootChoice`, `complexSquareRootChoice_mul_self`, and
   `sourceComplexDiagonal_factorization_self`.  The orthogonal-basis
   diagonalization spine is checked as
   `bilinform_orthogonal_basis_expansion`,
   `sourceMatrix_toBilin_isSymm`,
   `sourceSymmetricMatrix_exists_orthogonal_coordinate_expansion`,
   `sourceSymmetricMatrix_factorization_finrank`, and
   `sourceSymmetricMatrix_factorization_self`.  Thus the unrestricted complex
   symmetric factorization `Z = A * Aᵀ` in `n` coordinates is done.  The
   rank-compressed factorization is now also checked as
   `complex_symmetric_matrix_factorization_of_rank_le`, using a basis
   congruence to identify the number of nonzero diagonal weights with
   `Matrix.rank` and then reindexing those weights into `Fin D`.  The
   rank-defined reverse inclusion into the source complex Gram variety is
   checked as `sourceComplexGramVariety_mem_of_symmetric_rank_le`.
2. The minor-to-rank bridge for the current determinantal definition of
   `sourceSymmetricRankLEVariety` is now checked as
   `sourceMatrix_rank_le_of_minors_eq_zero`, with the finite row/column
   extraction support lemmas `exists_linearIndependent_rows_of_rank_ge` and
   `exists_nondegenerate_square_submatrix_of_rank_ge`.  The full source
   variety identification is now checked as
   `sourceComplexGramVariety_eq_rank_le`.  This is the algebraic
   Hall-Wightman input, not a theorem-2 shortcut and not a wrapper.

Lean-ready transcript for the reverse factorization theorem:

Hall-Wightman use this as the standard algebra input immediately after Lemma 2:
an arbitrary complex symmetric matrix of rank `r` is congruent to a diagonal
matrix with an `r × r` identity block and zeros elsewhere, hence is a scalar
product matrix of vectors spanning an `r`-dimensional complex space.  In Lean,
the most direct route should use mathlib's quadratic-form diagonalization over
fields with invertible `2`, plus the algebraically closed square-root step over
`ℂ`.

The preferred implementation should first prove the rank-based factorization,
then connect the minor-based variety to matrix rank if needed:

```lean
theorem BHW.complex_symmetric_matrix_factorization_of_rank_le
    (n D : ℕ)
    {Z : Fin n -> Fin n -> ℂ}
    (hZsym : ∀ i j, Z i j = Z j i)
    (hrank : (Matrix.of fun i j : Fin n => Z i j).rank ≤ D) :
    ∃ A : Fin n -> Fin D -> ℂ,
      Z = fun i j => ∑ a : Fin D, A i a * A j a
```

Proof steps:

1. Let `M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z i j`.
   Convert `hZsym` to `M.IsSymm`.
2. Let `B : LinearMap.BilinForm ℂ (Fin n -> ℂ) := Matrix.toBilin' M`.
   Use `Matrix.toBilin'`/`BilinForm.toMatrix'_toBilin'` to identify
   `B (Pi.single i 1) (Pi.single j 1)` with `Z i j`.
3. Use `LinearMap.BilinForm.exists_orthogonal_basis` to choose an orthogonal
   basis
   `b : Basis (Fin (Module.finrank ℂ (Fin n -> ℂ))) ℂ (Fin n -> ℂ)` for `B`;
   write
   `λ a := B (b a) (b a)`.
4. Prove the coordinate expansion

   ```lean
   theorem BHW.bilinform_orthogonal_basis_expansion
       {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
       [Fintype ι] [DecidableEq ι]
       (B : LinearMap.BilinForm K V)
       (b : Basis ι K V)
       (hortho : B.IsOrthoᵢ b)
       (x y : V) :
       B x y =
         ∑ a : ι, b.repr x a * b.repr y a * B (b a) (b a)
   ```

   by expanding `x` and `y` in the basis and using bilinearity plus
   orthogonality to kill off-diagonal terms.  This theorem is now checked.
5. Use `IsAlgClosed.exists_eq_mul_self` on each `λ a` to choose square roots
   `s a` with `s a * s a = λ a`.  Applying the checked expansion at
   `Pi.single i 1`, `Pi.single j 1` and rewriting `λ a = s a * s a` gives the
   checked unrestricted factorization

   ```lean
   theorem BHW.sourceSymmetricMatrix_factorization_self
       (n : ℕ)
       {Z : Fin n -> Fin n -> ℂ}
       (hZsym : Z ∈ BHW.sourceSymmetricMatrixSpace n) :
       ∃ A : Fin n -> Fin n -> ℂ,
         Z = BHW.sourceComplexDotGram n n A
   ```

6. Relate the number of nonzero `λ a` to `M.rank`.  The diagonal matrix of
   `B` in the basis has rank equal to the cardinality of `{a | λ a ≠ 0}`, and
   congruence by the basis-change matrix preserves rank.  Therefore
   `hrank` gives an injection

   ```lean
   nzIndex :
     {a : Fin (Module.finrank ℂ (Fin n -> ℂ)) // λ a ≠ 0} -> Fin D
   ```

   or equivalently a placement map of the nonzero diagonal entries into
   `Fin D`.
7. Define

   ```lean
   A i β :=
     if h : ∃ a, λ a ≠ 0 ∧ nzIndex ⟨a, ‹λ a ≠ 0›⟩ = β then
       let a := Classical.choose h
       s a * b.repr (Pi.single i 1) a
     else 0
   ```

   A cleaner implementation may choose an equivalence between the finite
   nonzero-weight subtype and a subtype of `Fin D`, then define `A` by
   `Subtype` recursion; the point is that zero `λ` coordinates contribute
   nothing.
8. Apply the checked expansion/factorization from steps 4-5 and reindex the
   nonzero finite sum through `nzIndex` to obtain
   `Z i j = ∑ β : Fin D, A i β * A j β`.  Steps 6-8 are now production-checked
   as `complex_symmetric_matrix_factorization_of_rank_le`.

The independent minor-to-rank bridge is now production-checked:

```lean
theorem BHW.sourceMatrix_rank_le_of_minors_eq_zero
    (n D : ℕ)
    {Z : Fin n -> Fin n -> ℂ}
    (hminors : ∀ I J : Fin (D + 1) -> Fin n,
      BHW.sourceMatrixMinor n (D + 1) I J Z = 0) :
    (Matrix.of fun i j : Fin n => Z i j).rank ≤ D

theorem BHW.sourceComplexGramVariety_eq_rank_le
    (d n : ℕ) :
    BHW.sourceComplexGramVariety d n =
      {Z | Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
        (Matrix.of fun i j : Fin n => Z i j).rank ≤ d + 1}
```

This bridge is pure finite-dimensional linear algebra: if matrix rank were
`> D`, choose `D + 1` linearly independent rows and then `D + 1` independent
columns in their span to produce a nonzero `(D + 1)` minor, contradicting
`hminors`.  It should not mention OS, Wightman, or source configurations.

Checked transcript for the minor-to-rank bridge:

```lean
theorem BHW.exists_linearIndependent_rows_of_rank_ge
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) {k : ℕ}
    (hk : k ≤ A.rank) :
    ∃ I : Fin k -> m,
      LinearIndependent ℂ (fun a : Fin k => A.row (I a))

theorem BHW.exists_nondegenerate_square_submatrix_of_rank_ge
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) {k : ℕ}
    (hk : k ≤ A.rank) :
    ∃ I : Fin k -> m, ∃ J : Fin k -> n,
      (Matrix.det (fun a b : Fin k => A (I a) (J b))) ≠ 0
```

Proof details:

1. Apply mathlib's indexed basis extraction
   `exists_linearIndependent' ℂ A.row` to the row family.  It returns an
   injective selector `a : κ -> m` whose selected rows are linearly independent
   and span the same submodule as all rows.
2. Since `a` injects into finite `m`, instantiate `Fintype κ` by
   `Finite.of_injective a ha_inj` and `Fintype.ofFinite κ`.
3. Use
   `linearIndependent_iff_card_eq_finrank_span.mp hli`, the span equality from
   step 1, and `Matrix.rank_eq_finrank_span_row` to prove
   `Fintype.card κ = A.rank`.
4. From `k ≤ A.rank`, use
   `Function.Embedding.nonempty_iff_card_le` to choose an embedding
   `e : Fin k ↪ κ`; compose the selected independent rows with `e`.
5. For the square-minor theorem, apply the row-selection lemma to `A` and
   `k ≤ A.rank`.  Let `R : Matrix (Fin k) n ℂ` be the selected-row matrix.
   The selected rows are linearly independent, hence
   `R.rank = k` by `LinearIndependent.rank_matrix`.
6. Use `Matrix.rank_transpose` and apply the row-selection lemma to `Rᵀ`.
   This chooses columns `J : Fin k -> n` such that the corresponding columns
   of `R` are linearly independent.
7. Let `S : Matrix (Fin k) (Fin k) ℂ := fun a b => A (I a) (J b)`.
   The previous column independence is `LinearIndependent ℂ S.col`; convert it
   to invertibility with `Matrix.linearIndependent_cols_iff_isUnit`, then to a
   nonzero determinant with `Matrix.isUnit_iff_isUnit_det`.
8. In `sourceMatrix_rank_le_of_minors_eq_zero`, argue by contradiction.  From
   `¬ M.rank ≤ D`, get `D + 1 ≤ M.rank`, extract `I,J` with nonzero determinant
   by step 7, and contradict `hminors I J` after unfolding
   `sourceMatrixMinor`.

`SCV.IsComplexAnalyticSet` and `SCV.AnalyticallyIrreducible` are not yet
production types.  If introducing that general SCV layer would grow the proof
too broadly, implement the specialized
`sourceComplexGramVariety_identity_principle` directly and keep the analytic
set, irreducibility, and identity-continuation facts above as private/internal
proof stages.  Either way, the singular lower-rank points must be handled by
the analytic-variety identity theorem, not by an unsupported regular-locus
connectedness claim.

The tempting source-space pullback shortcut is not a replacement for the
analytic-variety identity theorem unless it proves the same irreducibility
content.  Pulling back to
`{z | sourceMinkowskiGram d n z ∈ U}` makes `H ∘ sourceMinkowskiGram`
ordinary holomorphic on an open subset of source vector space, but ordinary
identity propagation only works on connected components of that preimage.  It
does not by itself show that every component maps onto the connected
variety-domain `U`, nor that zero on one lifted component reaches singular
lower-rank matrices.  Any pullback proof must therefore include a theorem
equivalent to irreducibility/monodromy of the Gram map over the rank variety.
Without that theorem, the pullback route is too weak and should not enter
production.

Follow-up Deep Research audit
`v1_ChdlemZ2YWY2Q0tZaWJfdU1QaDlHeDBBRRIXZXpmdmFmNkNLWWliX3VNUGg5R3gwQUU`
completed after the zero-form packet above.  Its useful correction is not a
new theorem surface, but a more implementable proof transcript for the global
identity theorem.  Instead of trying to introduce a broad generic
`SCV.AnalyticallyIrreducible` API first, the specialized source proof can work
through the regular rank stratum:

```lean
def BHW.sourceSymmetricRankExactStratum
    (n r : ℕ) : Set (Fin n -> Fin n -> ℂ) :=
  BHW.sourceSymmetricRankLEVariety n r \
    BHW.sourceSymmetricRankLEVariety n (r - 1)

theorem BHW.sourceSymmetricRankExactStratum_schur_chart
    (n r : ℕ)
    {I : Fin r -> Fin n}
    (hI : Function.Injective I) :
    -- On the open patch where the selected r x r principal minor is nonzero,
    -- the rank-exact symmetric stratum is parameterized by the symmetric
    -- selected block A and the off-block B, with C = Bᵀ A⁻¹ B.
    True

theorem BHW.sourceSymmetricRankLEVariety_regularLocus_eq_rankExact
    (n D : ℕ) (hD : D < n) :
    -- The regular locus of rank ≤ D symmetric matrices is the rank-exact D
    -- stratum; the singular locus is rank ≤ D - 1.
    True

theorem BHW.sourceSymmetricRankLEVariety_singular_codim_ge_two
    (n D : ℕ) (hD : D < n) :
    -- In the rank ≤ D symmetric variety, the rank ≤ D - 1 locus has complex
    -- codimension n - D + 1, hence at least 2.
    2 ≤ n - D + 1

theorem BHW.sourceSymmetricRankLEVariety_normal_or_locally_irreducible
    (n D : ℕ) :
    -- Either prove normality of the symmetric determinantal variety, or prove
    -- directly the local irreducibility consequence needed below.
    SCV.LocallyIrreducibleAnalyticSet
      (BHW.sourceSymmetricRankLEVariety n D)

theorem BHW.sourceSymmetricRankLEVariety_regularLocus_connected_dense
    (n D : ℕ) (hD : D < n)
    {U : Set (Fin n -> Fin n -> ℂ)}
    (hU_rel : ∃ U0, IsOpen U0 ∧
      U = U0 ∩ BHW.sourceSymmetricRankLEVariety n D)
    (hU_conn : IsConnected U)
    (hU_ne : U.Nonempty) :
    IsConnected
      (U ∩ BHW.sourceSymmetricRankExactStratum n D) ∧
    DenseIn
      (U ∩ BHW.sourceSymmetricRankExactStratum n D) U
```

The Schur-complement chart proof is elementary and should be the first
implementation target if the global identity theorem is attacked directly:

0. first expose the already-available complex regular chart, not only the
   real-slice version.  The checked complex differential theorem
   `sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero`
   gives the exact IFT hypothesis at any complex source point with nonzero
   selected minor:

   ```lean
   theorem BHW.sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor
       (d n : ℕ)
       {z0 : Fin n -> Fin (d + 1) -> ℂ}
       {I : Fin (min n (d + 1)) -> Fin n}
       {J : Fin (min n (d + 1)) -> Fin (d + 1)}
       (hI : Function.Injective I)
       (hJ : Function.Injective J)
       (hminor : BHW.sourceComplexRegularMinor d n I J z0 ≠ 0) :
       ∃ e : OpenPartialHomeomorph
           (Fin n -> Fin (d + 1) -> ℂ)
           (BHW.sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
             LinearMap.ker
               (BHW.sourceSelectedComplexGramDifferentialToSym d n
                 (min n (d + 1)) z0 I)),
         z0 ∈ e.source ∧
         e z0 =
           (BHW.sourceSelectedComplexGramMap d n (min n (d + 1)) I z0, 0) ∧
         ∀ z ∈ e.source,
           (e z).1 =
             BHW.sourceSelectedComplexGramMap d n (min n (d + 1)) I z
   ```

   Proof transcript: set `m := min n (d + 1)`,
   `f := sourceSelectedComplexGramMap d n m I`, and
   `f' := LinearMap.toContinuousLinearMap
       (sourceSelectedComplexGramDifferentialToSym d n m z0 I)`.
   Use `sourceSelectedComplexGramMap_hasStrictFDerivAt` at `z0`, convert
   surjectivity by
   `sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero`,
   and apply mathlib's
   `HasStrictFDerivAt.implicitToOpenPartialHomeomorph`.  The three conclusions
   are exactly `mem_implicitToOpenPartialHomeomorph_source`,
   `implicitToOpenPartialHomeomorph_self`, and
   `implicitToOpenPartialHomeomorph_fst`.  This theorem is now checked in
   `BHWPermutation/SourceComplexChart.lean`.
0a. prove that these nonzero-minor charts cover exactly the complex regular
    source configurations:

   ```lean
   theorem BHW.exists_nonzero_complex_coordinate_minor_of_linearIndependent
       {m D : ℕ}
       {v : Fin m -> Fin D -> ℂ}
       (hli : LinearIndependent ℂ v) :
       ∃ J : Fin m -> Fin D,
         Function.Injective J ∧
         Matrix.det (fun a b => v a (J b)) ≠ 0

   theorem BHW.sourceComplexGramRegularAt_of_exists_nonzero_minor
       (d n : ℕ)
       {z : Fin n -> Fin (d + 1) -> ℂ}
       (hminor :
         ∃ I : Fin (min n (d + 1)) -> Fin n,
           Function.Injective I ∧
           ∃ J : Fin (min n (d + 1)) -> Fin (d + 1),
             Function.Injective J ∧
             BHW.sourceComplexRegularMinor d n I J z ≠ 0) :
       BHW.SourceComplexGramRegularAt d n z

   theorem BHW.exists_nonzero_minor_of_sourceComplexGramRegularAt
       (d n : ℕ)
       {z : Fin n -> Fin (d + 1) -> ℂ}
       (hreg : BHW.SourceComplexGramRegularAt d n z) :
       ∃ I : Fin (min n (d + 1)) -> Fin n,
         Function.Injective I ∧
         ∃ J : Fin (min n (d + 1)) -> Fin (d + 1),
           Function.Injective J ∧
           BHW.sourceComplexRegularMinor d n I J z ≠ 0

   theorem BHW.sourceComplexGramRegularAt_iff_exists_nonzero_minor
       (d n : ℕ)
       (z : Fin n -> Fin (d + 1) -> ℂ) :
       BHW.SourceComplexGramRegularAt d n z ↔
         ∃ I : Fin (min n (d + 1)) -> Fin n,
           Function.Injective I ∧
           ∃ J : Fin (min n (d + 1)) -> Fin (d + 1),
             Function.Injective J ∧
             BHW.sourceComplexRegularMinor d n I J z ≠ 0

   theorem BHW.isOpen_sourceComplexGramRegularAt
       (d n : ℕ) :
       IsOpen {z : Fin n -> Fin (d + 1) -> ℂ |
         BHW.SourceComplexGramRegularAt d n z}
   ```

   Proof transcript: the coordinate-minor extraction is the same row/column
   argument as the real theorem, over `ℂ`: convert a linearly independent
   family `v : Fin m -> Fin D -> ℂ` to a matrix `A`, identify row and column
   ranks with `Matrix.rank_eq_finrank_span_row` and
   `Matrix.rank_eq_finrank_span_cols`, choose `m` independent columns by
   `Submodule.exists_fun_fin_finrank_span_eq`, and use
   `Matrix.linearIndependent_cols_iff_isUnit` to get nonzero determinant.
   The `sourceComplexGramRegularAt_of_exists_nonzero_minor` direction restricts
   source vectors to the selected coordinate columns and obtains a lower bound
   `min n (d+1) ≤ finrank span`; the upper bound is
   `min` of `finrank_range_le_card` and `Submodule.finrank_le`.  The reverse
   direction selects a basis-sized family from the source span by
   `Submodule.exists_fun_fin_finrank_span_eq`, chooses the corresponding source
   row indices, proves injectivity from linear independence, then applies the
   coordinate-minor extraction theorem.  Openness rewrites the regular set as
   the finite union over selected row/column maps of the nonzero locus of
   `sourceComplexRegularMinor`, using `continuous_sourceComplexRegularMinor`.
   This packet is now checked in `BHWPermutation/SourceComplexChart.lean`.
0b. expose the complex-regular local relative-open image theorem, the direct
    regular-stratum analogue of the checked real-regular theorem:

   ```lean
   theorem BHW.sourceComplexGramMap_localRelOpenImage_in_open_of_complexRegular
       (d n : ℕ)
       {z0 : Fin n -> Fin (d + 1) -> ℂ}
       (hreg : BHW.SourceComplexGramRegularAt d n z0)
       {V : Set (Fin n -> Fin (d + 1) -> ℂ)}
       (hV_open : IsOpen V)
       (hz0V : z0 ∈ V) :
       ∃ U : Set (Fin n -> Fin (d + 1) -> ℂ),
         IsOpen U ∧ z0 ∈ U ∧ U ⊆ V ∧
         ∃ O : Set (Fin n -> Fin n -> ℂ),
           BHW.sourceMinkowskiGram d n z0 ∈ O ∧
           BHW.IsRelOpenInSourceComplexGramVariety d n O ∧
           O ⊆ BHW.sourceMinkowskiGram d n '' U ∧
           ∀ G ∈ O, ∃ z ∈ U,
             BHW.sourceMinkowskiGram d n z = G
   ```

   Proof transcript: choose a nonzero complex maximal minor from
   `exists_nonzero_minor_of_sourceComplexGramRegularAt`; apply
   `sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor`.
   Shrink
   `U := (e.source ∩ {z | sourceComplexRegularMinor d n I J z ≠ 0}) ∩ V`.
   Let `T := e '' U`, `R := Prod.fst '' T`, and express the open set `R` in
   the induced topology on `sourceSelectedComplexSymCoordSubspace` as
   `Subtype.val ⁻¹' R0`.  Set
   `E0 := {G | sourceSelectedComplexGramCoord n m I G ∈ R0}` and
   `O := E0 ∩ sourceComplexGramVariety d n`.  Relative openness follows from
   continuity of the selected-coordinate projection.  For `G ∈ O`, select
   `u ∈ U` with the same selected coordinates and use
   `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety`
   plus the nonzero minor on `U` to prove
   `sourceMinkowskiGram d n u = G`.  This theorem is now checked in
   `BHWPermutation/SourceComplexChart.lean`.
0c. expose the rank-defined API for the minor-defined symmetric variety.  The
    global identity theorem must move between Hall-Wightman's determinantal
    equations and the rank-exact regular/singular strata; the current production
    definition is minor-defined, so the next support packet is:

   ```lean
   theorem BHW.matrix_rank_ge_of_nondegenerate_square_submatrix
       {m n : Type*} [Fintype m] [Fintype n]
       [DecidableEq m] [DecidableEq n]
       (A : Matrix m n ℂ) {k : ℕ}
       {I : Fin k -> m} {J : Fin k -> n}
       (hdet : Matrix.det (fun a b : Fin k => A (I a) (J b)) ≠ 0) :
       k ≤ A.rank

   theorem BHW.sourceMatrix_minors_eq_zero_of_rank_le
       (n D : ℕ) {Z : Fin n -> Fin n -> ℂ}
       (hrank : (Matrix.of fun i j : Fin n => Z i j).rank ≤ D) :
       ∀ I J : Fin (D + 1) -> Fin n,
         BHW.sourceMatrixMinor n (D + 1) I J Z = 0

   theorem BHW.sourceSymmetricRankLEVariety_eq_rank_le
       (n D : ℕ) :
       BHW.sourceSymmetricRankLEVariety n D =
         {Z | Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
           (Matrix.of fun i j : Fin n => Z i j).rank ≤ D}

   def BHW.sourceSymmetricRankExactStratum
       (n r : ℕ) : Set (Fin n -> Fin n -> ℂ) :=
     {Z | Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
       (Matrix.of fun i j : Fin n => Z i j).rank = r}

   theorem BHW.sourceSymmetricRankExactStratum_subset_rankLE
       (n r D : ℕ) (hrD : r ≤ D) :
       BHW.sourceSymmetricRankExactStratum n r ⊆
         BHW.sourceSymmetricRankLEVariety n D

   theorem BHW.sourceSymmetricRankExactStratum_eq_rankLE_diff
       (n r : ℕ) (hr : 0 < r) :
       BHW.sourceSymmetricRankExactStratum n r =
         BHW.sourceSymmetricRankLEVariety n r \
           BHW.sourceSymmetricRankLEVariety n (r - 1)

   theorem BHW.sourceComplexGramVariety_eq_rank_le
       (d n : ℕ) :
       BHW.sourceComplexGramVariety d n =
         {Z | Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
           (Matrix.of fun i j : Fin n => Z i j).rank ≤ d + 1}

   theorem BHW.sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
       (d n r : ℕ) (hr : r ≤ d + 1) :
       BHW.sourceSymmetricRankExactStratum n r ⊆
         BHW.sourceComplexGramVariety d n
   ```

   Proof transcript:

   1. For `matrix_rank_ge_of_nondegenerate_square_submatrix`, set
      `S : Matrix (Fin k) (Fin k) ℂ := fun a b => A (I a) (J b)`.  From
      `hdet`, use `Matrix.linearIndependent_rows_of_det_ne_zero` and
      `LinearIndependent.rank_matrix` to get `S.rank = k`.
   2. Let `R : Matrix (Fin k) n ℂ := fun a j => A (I a) j`.  Apply
      `Matrix.rank_submatrix_le` to `Rᵀ` with row selector `J` and identity
      column equivalence to get `Sᵀ.rank ≤ Rᵀ.rank`; simplify by
      `Matrix.rank_transpose`.
   3. Apply `Matrix.rank_submatrix_le` to `A` with row selector `I` and identity
      column equivalence to get `R.rank ≤ A.rank`.  Combine with step 1 to
      conclude `k ≤ A.rank`.
   4. For `sourceMatrix_minors_eq_zero_of_rank_le`, argue by contradiction on a
      selected `(D+1)×(D+1)` minor.  Step 3 gives `D+1 ≤ rank`; compose with
      `hrank` to contradict `Nat.not_succ_le_self D`.
   5. For `sourceSymmetricRankLEVariety_eq_rank_le`, split on `D < n`.  In the
      hard branch, the existing checked
      `sourceMatrix_rank_le_of_minors_eq_zero` gives minor-defined -> rank-defined
      and step 4 gives rank-defined -> minor-defined.  In the easy branch
      `¬ D < n`, the variety definition is only symmetry, and
      `Matrix.rank_le_width` plus `n ≤ D` supplies the rank bound.
   6. The exact stratum is deliberately rank-defined, not
      `rank≤r \ rank≤r-1`; this avoids a special-case error at `r = 0` and gives
      the regular/singular proofs the exact rank equation they use.
   7. For positive rank, prove the difference characterization by rewriting both
      `sourceSymmetricRankLEVariety` terms through
      `sourceSymmetricRankLEVariety_eq_rank_le`; the only arithmetic is
      `rank = r` iff `rank ≤ r` and not `rank ≤ r - 1`, with `0 < r`.
   8. The final two source-variety consumers are direct rewrites through
      `sourceComplexGramVariety_eq_rank_le` and the
      rank-defined characterization.  They are useful endpoints for the analytic
      continuation proof because the regular stratum lives inside
      `sourceComplexGramVariety d n` without reopening the minor definition.
0d. expose the closedness/continuity facts needed for the singular-closure
    stage of the global identity theorem:

   ```lean
   theorem BHW.continuous_sourceMatrixMinor
       (n k : ℕ)
       (I J : Fin k -> Fin n) :
       Continuous (BHW.sourceMatrixMinor n k I J)

   theorem BHW.isClosed_sourceSymmetricMatrixSpace
       (n : ℕ) :
       IsClosed (BHW.sourceSymmetricMatrixSpace n)

   theorem BHW.isClosed_sourceSymmetricRankLEVariety
       (n D : ℕ) :
       IsClosed (BHW.sourceSymmetricRankLEVariety n D)

   theorem BHW.isClosed_sourceComplexGramVariety
       (d n : ℕ) :
       IsClosed (BHW.sourceComplexGramVariety d n)
   ```

   Proof transcript: `continuous_sourceMatrixMinor` is
   `Continuous.matrix_det` applied to the continuous coordinate-submatrix map
   `Z ↦ fun a b => Z (I a) (J b)`.  Symmetric matrices are closed as the finite
   intersection of coordinate equalizer sets
   `{Z | Z i j = Z j i}`.  In the branch `D < n`,
   `sourceSymmetricRankLEVariety` is the intersection of the closed symmetric
   matrix space with the finite intersection of zero-sets of the continuous
   minors.  In the branch `¬ D < n`, it is just the symmetric matrix space.
   Closedness of `sourceComplexGramVariety` then rewrites through
   `sourceComplexGramVariety_eq_rank_le`.
   This packet is now checked in
   `BHWPermutation/SourceComplexGlobalIdentity.lean`.
0e. expose the first regular-locus topology fact needed for the global
    continuation theorem.  In Hall-Wightman's hard case the regular locus of
    the rank-`≤ d+1` scalar-product variety is the rank-exact `d+1` stratum,
    and the lower-rank part is the singular locus.  The implementation should
    first prove the topological complement statement, because it is a direct
    finite-dimensional consequence of the checked rank API and closedness:

   ```lean
   theorem BHW.sourceComplexGramVariety_diff_lowerRank_eq_rankExact
       (d n : ℕ) :
       BHW.sourceComplexGramVariety d n \
           BHW.sourceSymmetricRankLEVariety n d =
         BHW.sourceSymmetricRankExactStratum n (d + 1)

   theorem BHW.sourceSymmetricRankExactStratum_relOpenIn_sourceComplexGramVariety
       (d n : ℕ) :
       BHW.IsRelOpenInSourceComplexGramVariety d n
         (BHW.sourceSymmetricRankExactStratum n (d + 1))
   ```

   Proof transcript: rewrite
   `sourceComplexGramVariety d n` as
   `sourceSymmetricRankLEVariety n (d + 1)`, then apply the positive-rank
   difference theorem
   `sourceSymmetricRankExactStratum_eq_rankLE_diff n (d + 1)`.  The positivity
   input is `Nat.succ_pos d`.  For relative openness, take the ambient open set
   to be `(sourceSymmetricRankLEVariety n d)ᶜ`, open by
   `isClosed_sourceSymmetricRankLEVariety`.  Its intersection with
   `sourceComplexGramVariety d n` is exactly the rank-exact stratum by the
   previous difference theorem and elementary set algebra.
   This packet is now checked in
   `BHWPermutation/SourceComplexGlobalIdentity.lean` as
   `sourceComplexGramVariety_diff_lowerRank_eq_rankExact` and
   `sourceSymmetricRankExactStratum_relOpenIn_sourceComplexGramVariety`.
0f. expose the Schur-complement obstruction on a regular principal-minor
    patch.  This is the finite-dimensional algebra behind Hall-Wightman's
    statement that, near a nonsingular rank-`D` point, the rank-bounded
    scalar-product variety is a graph over the nonsingular block and the
    off-block coordinates:

   ```lean
   theorem BHW.matrix_rank_ge_card_of_nondegenerate_square_submatrix
       {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
       [DecidableEq m] [DecidableEq n] [DecidableEq κ]
       (A : Matrix m n ℂ)
       {I : κ -> m} {J : κ -> n}
       (hdet : Matrix.det (fun a b : κ => A (I a) (J b)) ≠ 0) :
       Fintype.card κ ≤ A.rank

   theorem BHW.schur_complement_entry_eq_zero_of_rank_le
       {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (A : Matrix r r ℂ) (B : Matrix r q ℂ) (C : Matrix q q ℂ)
       (hA : IsUnit A.det)
       (hrank : (Matrix.fromBlocks A B Bᵀ C).rank ≤ Fintype.card r)
       (u v : q) :
       (C - Bᵀ * A⁻¹ * B) u v = 0
   ```

   Proof transcript:

   1. `matrix_rank_ge_card_of_nondegenerate_square_submatrix` is the
      cardinal-indexed version of the checked finite-minor rank lower bound.
      Let `S : Matrix κ κ ℂ := fun a b => A (I a) (J b)` and
      `R : Matrix κ n ℂ := fun a j => A (I a) j`.  From
      `det S ≠ 0`, `Matrix.linearIndependent_rows_of_det_ne_zero` and
      `LinearIndependent.rank_matrix` give `S.rank = Fintype.card κ`.
      The selected-column comparison is obtained by applying
      `Matrix.rank_submatrix_le` to `Rᵀ` with row selector `J`; the selected-row
      comparison is `Matrix.rank_submatrix_le` applied to `A` with row selector
      `I`.  Combining them gives `Fintype.card κ ≤ A.rank`.
   2. For the Schur obstruction, fix `u v : q` and suppose
      `Suv := (C - Bᵀ * A⁻¹ * B) u v ≠ 0`.  Select the principal `r × r`
      block together with the extra row `u` and extra column `v`, indexed by
      `r ⊕ Unit`.  The selected `(r+1) × (r+1)` submatrix is

      ```lean
      Matrix.fromBlocks A (fun i _ => B i v)
        (fun _ j => Bᵀ u j) (fun _ _ : Unit => C u v)
      ```

   3. Because `A.det` is a unit, instantiate `Invertible A` through
      `Matrix.isUnit_iff_isUnit_det`.  Mathlib's
      `Matrix.det_fromBlocks₁₁` gives the determinant of this selected block as
      `A.det * Suv`, nonzero by `hA.ne_zero` and `Suv ≠ 0`.
   4. Step 1 then forces
      `Fintype.card (r ⊕ Unit) ≤ (Matrix.fromBlocks A B Bᵀ C).rank`, i.e.
      `Fintype.card r + 1 ≤ rank`, contradicting `hrank`.

   This theorem is the first half of the local graph chart: rank `≤ r` forces
   every Schur-complement entry to vanish on a patch with invertible principal
   block.  The converse graph-to-rank direction should use
   `Matrix.fromBlocks_eq_of_invertible₁₁` and rank invariance under the two
   invertible triangular LDU factors, reducing to the block diagonal
   `fromBlocks A 0 0 0`.
   This obstruction half is now checked in
   `BHWPermutation/SourceComplexGlobalIdentity.lean` as
   `matrix_rank_ge_card_of_nondegenerate_square_submatrix` and
   `schur_complement_entry_eq_zero_of_rank_le`.
0g. prove the converse graph-to-rank half of the Schur chart:

   ```lean
   theorem BHW.rank_fromBlocks_zero₂₂_le_card_left
       {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (A : Matrix r r ℂ) :
       (Matrix.fromBlocks A (0 : Matrix r q ℂ) (0 : Matrix q r ℂ)
         (0 : Matrix q q ℂ)).rank ≤ Fintype.card r

   theorem BHW.rank_fromBlocks_le_of_schur_complement_eq_zero
       {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (A : Matrix r r ℂ) (B : Matrix r q ℂ) (C : Matrix q q ℂ)
       (hA : IsUnit A.det)
       (hschur : C - Bᵀ * A⁻¹ * B = 0) :
       (Matrix.fromBlocks A B Bᵀ C).rank ≤ Fintype.card r
   ```

   Proof transcript:

   1. For `rank_fromBlocks_zero₂₂_le_card_left`, let
      `M := Matrix.fromBlocks A 0 0 0` and
      `rowVec : r -> (r ⊕ q -> ℂ) := fun i => M.row (Sum.inl i)`.
      Every row of `M` lies in `span (range rowVec)`: left rows are generators,
      right rows are zero.  Rewrite rank by `Matrix.rank_eq_finrank_span_row`;
      `Submodule.finrank_mono` and `finrank_range_le_card rowVec` give the
      bound.
   2. For `rank_fromBlocks_le_of_schur_complement_eq_zero`, instantiate
      `Invertible A` from `Matrix.isUnit_iff_isUnit_det` and rewrite
      `⅟A = A⁻¹` by `Matrix.invOf_eq_nonsing_inv`.
   3. Apply mathlib's `Matrix.fromBlocks_eq_of_invertible₁₁`:

      ```lean
      fromBlocks A B Bᵀ C =
        L * fromBlocks A 0 0 (C - Bᵀ * ⅟A * B) * U
      ```

      with invertible block-triangular `L` and `U`.
   4. Use only rank monotonicity under multiplication,
      `Matrix.rank_mul_le_left` and `Matrix.rank_mul_le_right`, to bound the
      rank by the middle block.  The Schur-complement hypothesis rewrites the
      middle block to `fromBlocks A 0 0 0`, and step 1 finishes.

   Together with 0f, this proves the local set-theoretic graph equivalence on
   an invertible principal block: rank `≤ r` is equivalent to Schur-complement
   zero.  The remaining chart work is coordinate packaging: reindex an arbitrary
   selected principal minor to a `r ⊕ q` block decomposition and expose the
   graph map `(A,B) ↦ Bᵀ A⁻¹ B` as a holomorphic finite-coordinate function on
   the open set `IsUnit A.det`.
   This converse half is now checked in
   `BHWPermutation/SourceComplexGlobalIdentity.lean` as
   `rank_fromBlocks_zero₂₂_le_card_left` and
   `rank_fromBlocks_le_of_schur_complement_eq_zero`.
0h. package the canonical block Schur equivalence under an arbitrary coordinate
    reindexing.  This is the bridge from the canonical `r ⊕ q` block algebra to
    a selected principal-minor patch of the symmetric scalar-product matrix:

   ```lean
   theorem BHW.toBlocks₂₁_eq_transpose_toBlocks₁₂_of_symm
       {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       {M : Matrix (r ⊕ q) (r ⊕ q) ℂ}
       (hM : ∀ i j, M i j = M j i) :
       M.toBlocks₂₁ = M.toBlocks₁₂ᵀ

   theorem BHW.schur_complement_entry_eq_zero_of_rank_le_reindex
       {ι r q : Type*} [Fintype ι] [Fintype r] [Fintype q]
       [DecidableEq ι] [DecidableEq r] [DecidableEq q]
       (Z : Matrix ι ι ℂ)
       (e : ι ≃ r ⊕ q)
       (hZsym : ∀ i j, Z i j = Z j i)
       (hA : IsUnit ((Z.reindex e e).toBlocks₁₁.det))
       (hrank : Z.rank ≤ Fintype.card r)
       (u v : q) :
       ((Z.reindex e e).toBlocks₂₂ -
           (Z.reindex e e).toBlocks₁₂ᵀ *
             (Z.reindex e e).toBlocks₁₁⁻¹ *
             (Z.reindex e e).toBlocks₁₂) u v = 0

   theorem BHW.rank_le_of_reindexed_schur_complement_eq_zero
       {ι r q : Type*} [Fintype ι] [Fintype r] [Fintype q]
       [DecidableEq ι] [DecidableEq r] [DecidableEq q]
       (Z : Matrix ι ι ℂ)
       (e : ι ≃ r ⊕ q)
       (hZsym : ∀ i j, Z i j = Z j i)
       (hA : IsUnit ((Z.reindex e e).toBlocks₁₁.det))
       (hschur :
         (Z.reindex e e).toBlocks₂₂ -
             (Z.reindex e e).toBlocks₁₂ᵀ *
               (Z.reindex e e).toBlocks₁₁⁻¹ *
               (Z.reindex e e).toBlocks₁₂ = 0) :
       Z.rank ≤ Fintype.card r
   ```

   Proof transcript:

   1. Symmetry of a block matrix gives
      `M.toBlocks₂₁ = M.toBlocks₁₂ᵀ` by extensionality on the lower-left
      block.
   2. Given `Z : Matrix ι ι ℂ` and `e : ι ≃ r ⊕ q`, set
      `M := Z.reindex e e`, `A := M.toBlocks₁₁`, `B := M.toBlocks₁₂`, and
      `C := M.toBlocks₂₂`.  Symmetry of `Z` transports to symmetry of `M` by
      `Matrix.reindex_apply`; step 1 identifies the lower-left block with
      `Bᵀ`.
   3. Use `Matrix.fromBlocks_toBlocks M` and the lower-left identity to prove
      `Matrix.fromBlocks A B Bᵀ C = M`.
   4. Rank is invariant under `Matrix.reindex` by `Matrix.rank_reindex`.  Thus
      rank hypotheses on `Z` transfer to the canonical block matrix and rank
      conclusions for the canonical block transfer back to `Z`.
   5. Apply the checked canonical Schur obstruction and converse from 0f-0g.

	   This gives the exact Lean bridge needed for arbitrary selected-coordinate
	   patches once a complement equivalence `Fin n ≃ Fin r ⊕ q` has been chosen.
	   This packet is now checked in
	   `BHWPermutation/SourceComplexGlobalIdentity.lean` as
	   `toBlocks₂₁_eq_transpose_toBlocks₁₂_of_symm`,
	   `schur_complement_entry_eq_zero_of_rank_le_reindex`, and
	   `rank_le_of_reindexed_schur_complement_eq_zero`.
	0i. expose the principal-patch graph characterization itself.  The Schur
	    algebra above is not yet the local Hall-Wightman chart until it is tied
	    back to the rank-exact/source-variety membership predicates.  The exact
	    finite statement needed downstream is:

	   ```lean
	   theorem BHW.rank_eq_card_iff_reindexed_schur_complement_eq_zero
	       {ι r q : Type*} [Fintype ι] [Fintype r] [Fintype q]
	       [DecidableEq ι] [DecidableEq r] [DecidableEq q]
	       (Z : Matrix ι ι ℂ)
	       (e : ι ≃ r ⊕ q)
	       (hZsym : ∀ i j, Z i j = Z j i)
	       (hA : IsUnit ((Z.reindex e e).toBlocks₁₁.det)) :
	       Z.rank = Fintype.card r ↔
	         (Z.reindex e e).toBlocks₂₂ -
	             (Z.reindex e e).toBlocks₁₂ᵀ *
	               (Z.reindex e e).toBlocks₁₁⁻¹ *
	               (Z.reindex e e).toBlocks₁₂ = 0

	   theorem BHW.sourceSymmetricRankExactStratum_iff_reindexed_schur_complement_eq_zero
	       (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
	       [DecidableEq r] [DecidableEq q]
	       (e : Fin n ≃ r ⊕ q)
	       {Z : Fin n -> Fin n -> ℂ}
	       (hA : IsUnit
	         (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁.det)) :
	       Z ∈ BHW.sourceSymmetricRankExactStratum n (Fintype.card r) ↔
	         Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
	           ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₂₂ -
	             ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂ᵀ *
	               ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁⁻¹ *
	               ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂ = 0

	   theorem BHW.sourceComplexGramVariety_iff_reindexed_schur_complement_eq_zero
	       (d n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
	       [DecidableEq r] [DecidableEq q]
	       (e : Fin n ≃ r ⊕ q)
	       (hcard : Fintype.card r = d + 1)
	       {Z : Fin n -> Fin n -> ℂ}
	       (hA : IsUnit
	         (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁.det)) :
	       Z ∈ BHW.sourceComplexGramVariety d n ↔
	         Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
	           ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₂₂ -
	             ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂ᵀ *
	               ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁⁻¹ *
	               ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂ = 0
	   ```

	   Proof transcript:

	   1. For the matrix rank equivalence, the forward direction turns
	      `Z.rank = card r` into `Z.rank ≤ card r` and applies
	      `schur_complement_entry_eq_zero_of_rank_le_reindex` to every entry.
	   2. Conversely, Schur-complement zero gives `Z.rank ≤ card r` by
	      `rank_le_of_reindexed_schur_complement_eq_zero`.  The invertible
	      principal block gives the opposite inequality by applying
	      `matrix_rank_ge_card_of_nondegenerate_square_submatrix` to
	      `M := Z.reindex e e` with row and column selectors `Sum.inl`; rank is
	      transported back by `Matrix.rank_reindex`.
	   3. The rank-exact source stratum theorem is just step 1 with
	      `M := Matrix.of fun i j => Z i j`, plus the symmetric-matrix predicate.
	      No analytic or QFT input appears.
	   4. The source-complex-variety theorem rewrites
	      `sourceComplexGramVariety d n` by `sourceComplexGramVariety_eq_rank_le`.
	      The invertible `card r = d+1` principal block upgrades the rank bound to
	      exact rank, and step 3 supplies the Schur graph equation.  This is the
	      precise local graph model Hall-Wightman use for the regular rank stratum.

	   This packet should live in a small companion file
	   `BHWPermutation/SourceComplexSchurPatch.lean`, importing the checked global
	   finite algebra.  It is genuine finite-dimensional scalar-product geometry:
	   it turns the Schur-complement lemmas into the actual local description of
	   the source Gram variety on a nonsingular principal-minor patch.
	0j. expose the rectangular Schur chart as the Lean implementation cover for
	    the regular rank stratum.  Hall-Wightman explicitly use the known
	    principal-minor rank fact for symmetric matrices; the current Lean
	    infrastructure already has the stronger all-minors extraction
	    `exists_nondegenerate_square_submatrix_of_rank_ge`.  To avoid making the
	    next stage depend on a separate principal-minor formalization, cover the
	    rank-exact stratum by arbitrary nonzero `r × r` minors and use independent
	    row/column reindexings:

	   ```lean
	   def BHW.reindexedRectSchurComplement
	       {ι κ r q₁ q₂ : Type*} [Fintype r] [DecidableEq r]
	       (Z : Matrix ι κ ℂ)
	       (er : ι ≃ r ⊕ q₁) (ec : κ ≃ r ⊕ q₂) :
	       Matrix q₁ q₂ ℂ

	   theorem BHW.rank_fromBlocks_zero₂₂_le_card_left_rect
	       {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
	       [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
	       (A : Matrix r r ℂ) :
	       (Matrix.fromBlocks A (0 : Matrix r q₂ ℂ) (0 : Matrix q₁ r ℂ)
	         (0 : Matrix q₁ q₂ ℂ)).rank ≤ Fintype.card r

	   theorem BHW.schur_complement_entry_eq_zero_of_rank_le_rect
	       {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
	       [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
	       (A : Matrix r r ℂ) (B : Matrix r q₂ ℂ)
	       (D : Matrix q₁ r ℂ) (C : Matrix q₁ q₂ ℂ)
	       (hA : IsUnit A.det)
	       (hrank : (Matrix.fromBlocks A B D C).rank ≤ Fintype.card r)
	       (u : q₁) (v : q₂) :
	       (C - D * A⁻¹ * B) u v = 0

	   theorem BHW.rank_fromBlocks_le_of_schur_complement_eq_zero_rect
	       {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
	       [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
	       (A : Matrix r r ℂ) (B : Matrix r q₂ ℂ)
	       (D : Matrix q₁ r ℂ) (C : Matrix q₁ q₂ ℂ)
	       (hA : IsUnit A.det)
	       (hschur : C - D * A⁻¹ * B = 0) :
	       (Matrix.fromBlocks A B D C).rank ≤ Fintype.card r

	   theorem BHW.rank_eq_card_iff_reindexed_rect_schur_complement_eq_zero
	       {ι κ r q₁ q₂ : Type*} [Fintype ι] [Fintype κ] [Fintype r]
	       [Fintype q₁] [Fintype q₂]
	       [DecidableEq ι] [DecidableEq κ] [DecidableEq r]
	       [DecidableEq q₁] [DecidableEq q₂]
	       (Z : Matrix ι κ ℂ)
	       (er : ι ≃ r ⊕ q₁) (ec : κ ≃ r ⊕ q₂)
	       (hA : IsUnit ((Z.reindex er ec).toBlocks₁₁.det)) :
	       Z.rank = Fintype.card r ↔
	         BHW.reindexedRectSchurComplement Z er ec = 0

	   theorem BHW.sourceSymmetricRankExactStratum_iff_reindexed_rect_schur_complement_eq_zero
	       (n : ℕ) {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
	       [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
	       (er : Fin n ≃ r ⊕ q₁) (ec : Fin n ≃ r ⊕ q₂)
	       {Z : Fin n -> Fin n -> ℂ}
	       (hA : IsUnit
	         (((Matrix.of fun i j : Fin n => Z i j).reindex er ec).toBlocks₁₁.det)) :
	       Z ∈ BHW.sourceSymmetricRankExactStratum n (Fintype.card r) ↔
	         Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
	           BHW.reindexedRectSchurComplement
	             (Matrix.of fun i j : Fin n => Z i j) er ec = 0

	   theorem BHW.sourceComplexGramVariety_iff_reindexed_rect_schur_complement_eq_zero
	       (d n : ℕ) {r q₁ q₂ : Type*} [Fintype r] [Fintype q₁] [Fintype q₂]
	       [DecidableEq r] [DecidableEq q₁] [DecidableEq q₂]
	       (er : Fin n ≃ r ⊕ q₁) (ec : Fin n ≃ r ⊕ q₂)
	       (hcard : Fintype.card r = d + 1)
	       {Z : Fin n -> Fin n -> ℂ}
	       (hA : IsUnit
	         (((Matrix.of fun i j : Fin n => Z i j).reindex er ec).toBlocks₁₁.det)) :
	       Z ∈ BHW.sourceComplexGramVariety d n ↔
	         Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
	           BHW.reindexedRectSchurComplement
	             (Matrix.of fun i j : Fin n => Z i j) er ec = 0

	   abbrev BHW.selectedIndexComplement
	       {r n : ℕ} (I : Fin r -> Fin n) : Type

	   noncomputable def BHW.selectedIndexSumEquiv
	       {r n : ℕ} (I : Fin r -> Fin n) (hI : Function.Injective I) :
	       Fin n ≃ Fin r ⊕ BHW.selectedIndexComplement I

	   theorem BHW.selectedIndexSumEquiv_apply_selected
	       {r n : ℕ} (I : Fin r -> Fin n) (hI : Function.Injective I)
	       (a : Fin r) :
	       BHW.selectedIndexSumEquiv I hI (I a) = Sum.inl a

	   theorem BHW.selectedIndexSumEquiv_toBlocks₁₁
	       {r n : ℕ} {I J : Fin r -> Fin n}
	       (hI : Function.Injective I) (hJ : Function.Injective J)
	       (Z : Fin n -> Fin n -> ℂ) :
	       (((Matrix.of fun i j : Fin n => Z i j).reindex
	           (BHW.selectedIndexSumEquiv I hI)
	           (BHW.selectedIndexSumEquiv J hJ)).toBlocks₁₁) =
	         (fun a b : Fin r => Z (I a) (J b))

	   theorem BHW.isUnit_selectedIndexSumEquiv_toBlocks₁₁_det
	       {r n : ℕ} {I J : Fin r -> Fin n}
	       (hI : Function.Injective I) (hJ : Function.Injective J)
	       {Z : Fin n -> Fin n -> ℂ}
	       (hdet : BHW.sourceMatrixMinor n r I J Z ≠ 0) :
	       IsUnit
	         ((((Matrix.of fun i j : Fin n => Z i j).reindex
	           (BHW.selectedIndexSumEquiv I hI)
	           (BHW.selectedIndexSumEquiv J hJ)).toBlocks₁₁).det)

	   theorem BHW.sourceComplexGramVariety_iff_selected_rect_schur_complement_eq_zero
	       (d n r : ℕ) {I J : Fin r -> Fin n}
	       (hI : Function.Injective I) (hJ : Function.Injective J)
	       (hr : r = d + 1)
	       {Z : Fin n -> Fin n -> ℂ}
	       (hdet : BHW.sourceMatrixMinor n r I J Z ≠ 0) :
	       Z ∈ BHW.sourceComplexGramVariety d n ↔
	         Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
	           BHW.reindexedRectSchurComplement
	             (Matrix.of fun i j : Fin n => Z i j)
	             (BHW.selectedIndexSumEquiv I hI)
	             (BHW.selectedIndexSumEquiv J hJ) = 0
	   ```

	   Proof transcript: the obstruction and converse are the same determinant/LDU
	   proof as 0f-0g, but for a general block matrix
	   `[[A,B],[D,C]]`.  The zero lower-right block rank bound uses the same row
	   span argument, now with different lower-row and right-column complements.
	   The reindexed theorem transports rank through independent `Matrix.reindex`
	   equivalences.  The source-variety theorem rewrites
	   `sourceComplexGramVariety` by `sourceComplexGramVariety_eq_rank_le`, uses
	   the invertible selected block to upgrade `rank ≤ d+1` to exact rank, and
	   applies the rectangular Schur equivalence.

	   The complement packaging uses `Equiv.sumCompl` for the selected image and
	   its complement, together with `Equiv.ofInjective I hI` to identify the
	   selected image with `Fin r`.  The upper-left block lemma proves that the
	   reindexed block is exactly the selected minor, so a nonzero selected minor
	   supplies the `IsUnit` hypothesis of the rectangular Schur theorem.

	   This packet is now checked in `BHWPermutation/SourceComplexSchurPatch.lean`.
	   It is faithful to Hall-Wightman's determinantal scalar-product variety:
	   principal-minor charts are still available, but the regular-stratum cover
	   can be implemented from the already checked nonzero all-minor extraction
	   without leaving a hidden complement-equivalence gap.
	0k. prove that the selected rectangular Schur charts actually cover the
	    rank-exact regular stratum.  The missing point after 0j is not another
	    graph formula but the cover extraction: an exact-rank source point must
	    supply a nonzero selected minor with injective row and column selectors,
	    so that the canonical complement equivalences from 0j apply.

	   ```lean
	   theorem BHW.sourceMatrixMinor_ne_zero_left_injective
	       {n r : ℕ} {I J : Fin r -> Fin n}
	       {Z : Fin n -> Fin n -> ℂ}
	       (hdet : BHW.sourceMatrixMinor n r I J Z ≠ 0) :
	       Function.Injective I

	   theorem BHW.sourceMatrixMinor_ne_zero_right_injective
	       {n r : ℕ} {I J : Fin r -> Fin n}
	       {Z : Fin n -> Fin n -> ℂ}
	       (hdet : BHW.sourceMatrixMinor n r I J Z ≠ 0) :
	       Function.Injective J

	   theorem BHW.exists_sourceMatrixMinor_ne_zero_of_sourceSymmetricRankExactStratum
	       {n r : ℕ} {Z : Fin n -> Fin n -> ℂ}
	       (hZ : Z ∈ BHW.sourceSymmetricRankExactStratum n r) :
	       ∃ I : Fin r -> Fin n, ∃ J : Fin r -> Fin n,
	         BHW.sourceMatrixMinor n r I J Z ≠ 0

	   theorem BHW.exists_selected_rect_schur_chart_of_sourceSymmetricRankExactStratum
	       {n r : ℕ} {Z : Fin n -> Fin n -> ℂ}
	       (hZ : Z ∈ BHW.sourceSymmetricRankExactStratum n r) :
	       ∃ I : Fin r -> Fin n, ∃ hI : Function.Injective I,
	       ∃ J : Fin r -> Fin n, ∃ hJ : Function.Injective J,
	         BHW.sourceMatrixMinor n r I J Z ≠ 0 ∧
	         Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
	           BHW.reindexedRectSchurComplement
	             (Matrix.of fun i j : Fin n => Z i j)
	             (BHW.selectedIndexSumEquiv I hI)
	             (BHW.selectedIndexSumEquiv J hJ) = 0

	   theorem BHW.exists_selected_rect_schur_chart_of_sourceComplexGramVariety_rankExact
	       {d n : ℕ} {Z : Fin n -> Fin n -> ℂ}
	       (hZ : Z ∈ BHW.sourceSymmetricRankExactStratum n (d + 1)) :
	       ∃ I : Fin (d + 1) -> Fin n, ∃ hI : Function.Injective I,
	       ∃ J : Fin (d + 1) -> Fin n, ∃ hJ : Function.Injective J,
	         BHW.sourceMatrixMinor n (d + 1) I J Z ≠ 0 ∧
	         (Z ∈ BHW.sourceComplexGramVariety d n ↔
	           Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
	             BHW.reindexedRectSchurComplement
	               (Matrix.of fun i j : Fin n => Z i j)
	               (BHW.selectedIndexSumEquiv I hI)
	               (BHW.selectedIndexSumEquiv J hJ) = 0) ∧
	         Z ∈ BHW.sourceComplexGramVariety d n ∧
	           BHW.reindexedRectSchurComplement
	             (Matrix.of fun i j : Fin n => Z i j)
	             (BHW.selectedIndexSumEquiv I hI)
	             (BHW.selectedIndexSumEquiv J hJ) = 0
	   ```

	   Proof transcript:

	   1. If `sourceMatrixMinor n r I J Z ≠ 0` and `I a = I b` with
	      `a ≠ b`, then the selected square matrix has two equal rows.  Apply
	      `Matrix.det_zero_of_row_eq` to contradict the nonzero determinant.
	      The column-selector proof is identical with
	      `Matrix.det_zero_of_column_eq`.
	   2. For a rank-exact source point, put
	      `M := Matrix.of fun i j : Fin n => Z i j`.  The exact-rank equation
	      gives `r ≤ M.rank`; apply the checked
	      `exists_nondegenerate_square_submatrix_of_rank_ge` to obtain selected
	      maps `I,J` with nonzero determinant, then rewrite that determinant as
	      `sourceMatrixMinor`.
	   3. Use step 1 to turn the nonzero determinant into injective selectors.
	      The selected-complement equivalences
	      `selectedIndexSumEquiv I hI` and `selectedIndexSumEquiv J hJ` are now
	      available, and `isUnit_selectedIndexSumEquiv_toBlocks₁₁_det` supplies
	      the invertible block hypothesis.
	   4. Apply
	      `sourceSymmetricRankExactStratum_iff_reindexed_rect_schur_complement_eq_zero`
	      to the exact-rank hypothesis.  This gives symmetry plus vanishing of
	      the selected rectangular Schur complement.
	   5. In the regular `d+1` source-complex case, apply
	      `sourceComplexGramVariety_iff_selected_rect_schur_complement_eq_zero`
	      to package the local graph equivalence for
	      `sourceComplexGramVariety d n`.  Membership of the exact-rank point in
	      the source complex Gram variety is supplied by
	      `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety`.

	   This packet is now checked in `BHWPermutation/SourceComplexSchurPatch.lean`.
	   The regular stratum is therefore covered by actual selected nonzero-minor
	   Schur graph charts, not merely by an abstract existence theorem.  The next
	   proof-doc target is the transition/dimension layer: holomorphicity of the
	   graph coordinates on determinant-nonzero patches, dimension of the
	   rank-exact stratum, codimension of the lower-rank locus, and the
	   irreducible analytic identity principle for the source scalar-product
	   variety.
	0l. record the relative-open topology of the selected Schur patches.  The
	    regular chart cover must be a cover by relatively open pieces of the
	    source scalar-product variety, not merely a pointwise algebraic cover.
	    The finite topology needed here is:

	   ```lean
	   theorem BHW.isOpen_sourceMatrixMinor_ne_zero
	       (n r : ℕ) (I J : Fin r -> Fin n) :
	       IsOpen {Z : Fin n -> Fin n -> ℂ |
	         BHW.sourceMatrixMinor n r I J Z ≠ 0}

	   theorem BHW.sourceMatrixMinor_ne_zero_relOpenInSourceComplexGramVariety
	       (d n r : ℕ) (I J : Fin r -> Fin n) :
	       BHW.IsRelOpenInSourceComplexGramVariety d n
	         ({Z : Fin n -> Fin n -> ℂ |
	           BHW.sourceMatrixMinor n r I J Z ≠ 0} ∩
	           BHW.sourceComplexGramVariety d n)

	   theorem BHW.sourceComplexGramVariety_regularSelectedMinorPatch_relOpen
	       (d n : ℕ) (I J : Fin (d + 1) -> Fin n) :
	       BHW.IsRelOpenInSourceComplexGramVariety d n
	         (BHW.sourceSymmetricRankExactStratum n (d + 1) ∩
	           {Z : Fin n -> Fin n -> ℂ |
	             BHW.sourceMatrixMinor n (d + 1) I J Z ≠ 0})
	   ```

	   Proof transcript:

	   1. `sourceMatrixMinor` is continuous by the already checked determinant
	      continuity theorem.  The nonzero locus is therefore open by
	      `isOpen_ne_fun`.
	   2. Relative openness in `sourceComplexGramVariety d n` is exactly an
	      ambient open set intersected with the variety, so the determinant
	      patch is immediate from step 1.
	   3. For the regular selected-minor patch, unpack
	      `sourceSymmetricRankExactStratum_relOpenIn_sourceComplexGramVariety`
	      as `rankExact = U0 ∩ sourceComplexGramVariety d n`, intersect the
	      ambient open set `U0` with the determinant-nonzero open set, and use
	      `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety` for
	      the set extensionality.

	   This packet is now checked in `BHWPermutation/SourceComplexSchurPatch.lean`.
	   The next layer is no longer the existence or openness of regular Schur
	   charts; it is the dimension/codimension and irreducibility content of
	   Hall-Wightman's scalar-product variety.
	0m. record the selected-chart dimension count over `ℂ`.  The selected
	    symmetric-coordinate chart for an `m`-row minor has exactly
	    `n*m - m*(m-1)/2` free complex coordinates: all `n*m` selected-column
	    coordinates, minus the `m*(m-1)/2` skew-symmetry constraints inside the
	    selected block.

	   ```lean
	   theorem BHW.finrank_sourceSelectedComplexSymCoordSubspace
	       (n m : ℕ)
	       (I : Fin m -> Fin n)
	       (hI : Function.Injective I) :
	       Module.finrank ℂ (BHW.sourceSelectedComplexSymCoordSubspace n m I) =
	         n * m - (m * (m - 1)) / 2
	   ```

	   Proof transcript:

	   1. Let `K := sourceSelectedSymCoordKey n m I`, the checked coordinate-key
	      type for the selected symmetric-coordinate subspace.
	   2. Use the already checked real continuous linear equivalence
	      `sourceSelectedRealSymCoordKeyEquiv n m hI` and the real dimension
	      theorem `finrank_sourceSelectedSymCoordSubspace n m I hI` to identify
	      `Fintype.card K` with `n*m - m*(m-1)/2`.
	   3. Use the checked complex continuous linear equivalence
	      `sourceSelectedComplexSymCoordKeyEquiv n m hI` to transfer the complex
	      finrank of `sourceSelectedComplexSymCoordSubspace n m I` to
	      `Module.finrank ℂ (K -> ℂ)`.
	   4. Finish by `Module.finrank_fintype_fun_eq_card` and the cardinal count
	      from step 2.

	   This is now checked in the small companion file
	   `BHWPermutation/SourceComplexDimension.lean`, imported by the
	   `BHWPermutation` umbrella.  For the regular rank-`D` stratum, substituting
	   `m = D` gives the Hall-Wightman dimension
	   `n*D - D*(D-1)/2`.  The next exact proof-doc packet is the lower-rank
	   codimension calculation:

	   ```text
	   dim(rankExact D) - dim(rankExact (D-1)) = n - D + 1.
	   ```

	   With `D = d + 1` and the singular case `D < n`, this gives codimension
	   at least `2`, the gap needed before the irreducible analytic identity
	   theorem.
	0n. compute the lower-rank codimension in the selected complex charts.  The
	    formula is purely finite-dimensional arithmetic, but it must be present
	    in Lean before the analytic identity theorem can cite "codimension at
	    least two" without handwaving.  The implementation uses the binomial
	    form `Nat.choose r 2` internally, then rewrites it to the paper formula
	    `r*(r-1)/2` by `Nat.choose_two_right`.

	   ```lean
	   theorem BHW.sourceRankExactChartDim_choose_two_le_mul
	       (n k : Nat) (hk : k <= n) :
	       Nat.choose k 2 <= n * k

	   theorem BHW.sourceRankExactChartDim_succ_sub_choose
	       (n k : Nat) (hk : k + 1 <= n) :
	       n * (k + 1) - Nat.choose (k + 1) 2 -
	           (n * k - Nat.choose k 2) =
	         n - k

	   theorem BHW.sourceRankExactChartDim_sub_previous_choose
	       (n D : Nat) (hD0 : 0 < D) (hDle : D <= n) :
	       n * D - Nat.choose D 2 -
	           (n * (D - 1) - Nat.choose (D - 1) 2) =
	         n - D + 1

	   theorem BHW.sourceRankExactChartDim_sub_previous
	       (n D : Nat) (hD0 : 0 < D) (hDle : D <= n) :
	       n * D - (D * (D - 1)) / 2 -
	           (n * (D - 1) - ((D - 1) * ((D - 1) - 1)) / 2) =
	         n - D + 1

	   theorem BHW.finrank_sourceSelectedComplexSymCoordSubspace_sub_previous
	       (n D : Nat) (hD0 : 0 < D) (hDle : D <= n)
	       (I : Fin D -> Fin n) (hI : Function.Injective I)
	       (J : Fin (D - 1) -> Fin n) (hJ : Function.Injective J) :
	       Module.finrank ℂ
	           (BHW.sourceSelectedComplexSymCoordSubspace n D I) -
	           Module.finrank ℂ
	             (BHW.sourceSelectedComplexSymCoordSubspace n (D - 1) J) =
	         n - D + 1

	   theorem BHW.finrank_sourceSelectedComplexSymCoordSubspace_lowerRankCodim_ge_two
	       (n D : Nat) (hD0 : 0 < D) (hDlt : D < n)
	       (I : Fin D -> Fin n) (hI : Function.Injective I)
	       (J : Fin (D - 1) -> Fin n) (hJ : Function.Injective J) :
	       2 <=
	         Module.finrank ℂ
	           (BHW.sourceSelectedComplexSymCoordSubspace n D I) -
	           Module.finrank ℂ
	             (BHW.sourceSelectedComplexSymCoordSubspace n (D - 1) J)
	   ```

	   Proof transcript:

	   1. Prove `Nat.choose k 2 <= n*k` under `k <= n` by rewriting
	      `Nat.choose k 2` as `k*(k-1)/2`, bounding division by the numerator,
	      then using `k*(k-1) <= k*k <= n*k`.
	   2. Prove the successor identity
	      `choose(k+1,2) = choose(k,2)+k` from
	      `Nat.choose_succ_succ`; after rewriting `n*(k+1)` by
	      `Nat.mul_succ`, `omega` closes the truncated-subtraction identity
	      using the bound from step 1.
	   3. For positive `D`, case-split `D = k+1` and apply the successor
	      identity to obtain
	      `dim(D) - dim(D-1) = n-D+1` in the binomial form.
	   4. Rewrite both binomial coefficients by `Nat.choose_two_right` to get
	      the paper's dimension formula
	      `n*D - D*(D-1)/2`.
	   5. Substitute the already checked selected complex chart finrank formula
	      for ranks `D` and `D-1`; this gives the actual selected-chart
	      codimension theorem.
	   6. If the lower-rank singular locus is present inside rank `<= D`, then
	      `D < n`; the arithmetic identity gives `2 <= n-D+1`, hence
	      codimension at least two.

	   This is the exact finite-dimensional Hall-Wightman arithmetic needed
	   before the source-variety identity principle.  It does not by itself
	   prove irreducibility or density of the regular stratum; those remain the
	   next analytic-variety obligations.
	0o. prove density of complex regular source configurations.  This is the
	    source-side density input for the regular-stratum part of the
	    Hall-Wightman scalar-product variety proof.  It is not a pullback
	    shortcut: it only says that maximal-span source configurations are dense
	    in the source vector space, and must later be combined with the Gram-map
	    local image theorem and the rank-exact/regular-stratum bridge.

	   ```lean
	   def BHW.sourceComplexFullSpanTemplate
	       (d n : Nat) : Fin n -> Fin (d + 1) -> ℂ :=
	     realEmbed (BHW.sourceFullSpanTemplate d n)

	   theorem BHW.sourceComplexFullSpanTemplate_basisVector
	       (d n : Nat) (a : Fin (min n (d + 1))) :
	       BHW.sourceComplexFullSpanTemplate d n
	           (BHW.sourceTemplateDomainIndex d n a) =
	         Pi.single (BHW.sourceTemplateCoordIndex d n a) (1 : ℂ)

	   theorem BHW.sourceComplexFullSpanTemplate_regularMinor_eq_one
	       (d n : Nat) :
	       BHW.sourceComplexRegularMinor d n
	           (BHW.sourceTemplateDomainIndex d n)
	           (BHW.sourceTemplateCoordIndex d n)
	           (BHW.sourceComplexFullSpanTemplate d n) = 1

	   theorem BHW.sourceComplexFullSpanTemplate_regularMinor_ne_zero
	       (d n : Nat) :
	       BHW.sourceComplexRegularMinor d n
	           (BHW.sourceTemplateDomainIndex d n)
	           (BHW.sourceTemplateCoordIndex d n)
	           (BHW.sourceComplexFullSpanTemplate d n) ≠ 0

	   def BHW.sourceComplexCanonicalRegularMinorLinePolynomial
	       (d n : Nat)
	       (z : Fin n -> Fin (d + 1) -> ℂ) : Polynomial ℂ

	   theorem BHW.sourceComplexCanonicalRegularMinorLinePolynomial_leadingCoeff
	       (d n : Nat)
	       (z : Fin n -> Fin (d + 1) -> ℂ) :
	       Polynomial.leadingCoeff
	         (BHW.sourceComplexCanonicalRegularMinorLinePolynomial d n z) = 1

	   theorem BHW.sourceComplexCanonicalRegularMinorLinePolynomial_ne_zero
	       (d n : Nat)
	       (z : Fin n -> Fin (d + 1) -> ℂ) :
	       BHW.sourceComplexCanonicalRegularMinorLinePolynomial d n z ≠ 0

	   theorem BHW.sourceComplexCanonicalRegularMinorLinePolynomial_eval
	       (d n : Nat)
	       (z : Fin n -> Fin (d + 1) -> ℂ)
	       (t : ℂ) :
	       (BHW.sourceComplexCanonicalRegularMinorLinePolynomial d n z).eval t =
	         BHW.sourceComplexRegularMinor d n
	           (BHW.sourceTemplateDomainIndex d n)
	           (BHW.sourceTemplateCoordIndex d n)
	           (z + t • BHW.sourceComplexFullSpanTemplate d n)

	   theorem BHW.sourceComplexCanonicalRegularMinor_nonzero_dense
	       (d n : Nat) :
	       Dense {z : Fin n -> Fin (d + 1) -> ℂ |
	         BHW.sourceComplexRegularMinor d n
	           (BHW.sourceTemplateDomainIndex d n)
	           (BHW.sourceTemplateCoordIndex d n) z ≠ 0}

	   theorem BHW.dense_sourceComplexGramRegularAt
	       (d n : Nat) :
	       Dense {z : Fin n -> Fin (d + 1) -> ℂ |
	         BHW.SourceComplexGramRegularAt d n z}
	   ```

	   Proof transcript:

	   1. Complexify the already checked real full-span template by
	      `realEmbed`.  The basis-vector theorem is obtained pointwise from
	      `sourceFullSpanTemplate_basisVector`, after casting `0` and `1` from
	      `ℝ` to `ℂ`.
	   2. The canonical complex regular minor of this template is `1` by
	      `sourceComplexRegularMinor_realEmbed` and
	      `sourceFullSpanTemplate_regularMinor_eq_one`; hence it is nonzero.
	   3. For any complex source configuration `z`, define the determinant
	      polynomial of the canonical minor along the complex line
	      `z + t • sourceComplexFullSpanTemplate d n`:

	      ```lean
	      Matrix.det (X • 1 + B.map Polynomial.C)
	      ```

	      where `B` is the selected coordinate block of `z`.
	   4. `Polynomial.leadingCoeff_det_X_one_add_C` gives leading coefficient
	      `1`, so the polynomial is nonzero.
	   5. Evaluating the polynomial at `t` equals the canonical complex regular
	      minor of `z + t • sourceComplexFullSpanTemplate d n`; the proof is the
	      same determinant/permutation expansion as the real dense-regular
	      theorem, using the complex basis-vector identity from step 1.
	   6. The zero set of a nonzero one-variable complex polynomial is finite,
	      hence its complement is dense in `ℂ`.  Given any nonempty open set in
	      source configuration space, pull it back along the continuous complex
	      line through a point of that open set and choose a parameter outside
	      the finite root set.  The corresponding source configuration lies in
	      the open set and has nonzero canonical regular minor.
	   7. The dense nonzero-minor locus is contained in
	      `SourceComplexGramRegularAt` by the already checked
	      `sourceComplexGramRegularAt_of_exists_nonzero_minor`, using the
	      canonical injective domain and coordinate selectors.

	   This packet should live in a new small companion file
	   `BHWPermutation/SourceComplexDensity.lean`, imported by the
	   `BHWPermutation` umbrella after `SourceComplexDimension`.  The next
	   density step after this is not another source-space statement: it is the
	   Gram-image regular-stratum bridge, showing how dense complex regular
	   sources yield dense rank-exact scalar-product matrices in the source
	   complex Gram variety.
	0p. prove the complex regular-source Gram-image rank-exact bridge in the
	    hard Hall-Wightman range `d + 1 <= n`.  This is the first source-density
	    transfer step after 0o: it shows that a complex source point with maximal
	    source span maps to the regular rank-`d+1` stratum of the source complex
	    Gram variety.  The hypothesis `d + 1 <= n` is essential.  If
	    `d + 1 > n`, the rank-`d+1` stratum in `n x n` Gram coordinates is empty;
	    moreover a smaller independent source family can span a degenerate
	    isotropic subspace, so source regularity alone does not force a
	    nondegenerate Gram matrix.  This packet is therefore not a wrapper around
	    regularity: it is the nondegenerate-pairing argument that transfers
	    regularity through the Minkowski Gram map.

	   ```lean
	   theorem BHW.sourceMinkowskiGram_rows_linearIndependent_of_sourceComplexRegularMinor_ne_zero
	       (d n : Nat)
	       {z : Fin n -> Fin (d + 1) -> ℂ}
	       {I : Fin (min n (d + 1)) -> Fin n}
	       {J : Fin (min n (d + 1)) -> Fin (d + 1)}
	       (hminor :
	         BHW.sourceComplexRegularMinor d n I J z ≠ 0)
	       (hD : d + 1 <= n) :
	       LinearIndependent ℂ
	         (fun a : Fin (min n (d + 1)) =>
	           fun j : Fin n => BHW.sourceMinkowskiGram d n z (I a) j)

	   theorem BHW.sourceMinkowskiGram_rank_ge_of_sourceComplexRegularMinor_ne_zero
	       (d n : Nat)
	       {z : Fin n -> Fin (d + 1) -> ℂ}
	       {I : Fin (min n (d + 1)) -> Fin n}
	       {J : Fin (min n (d + 1)) -> Fin (d + 1)}
	       (hminor :
	         BHW.sourceComplexRegularMinor d n I J z ≠ 0)
	       (hD : d + 1 <= n) :
	       d + 1 <=
	         (Matrix.of fun i j : Fin n =>
	           BHW.sourceMinkowskiGram d n z i j).rank

	   theorem BHW.sourceMinkowskiGram_rank_ge_of_sourceComplexGramRegularAt
	       (d n : Nat)
	       (hD : d + 1 <= n)
	       {z : Fin n -> Fin (d + 1) -> ℂ}
	       (hreg : BHW.SourceComplexGramRegularAt d n z) :
	       d + 1 <=
	         (Matrix.of fun i j : Fin n =>
	           BHW.sourceMinkowskiGram d n z i j).rank

	   theorem BHW.sourceMinkowskiGram_mem_rankExact_of_sourceComplexGramRegularAt
	       (d n : Nat)
	       (hD : d + 1 <= n)
	       {z : Fin n -> Fin (d + 1) -> ℂ}
	       (hreg : BHW.SourceComplexGramRegularAt d n z) :
	       BHW.sourceMinkowskiGram d n z ∈
	         BHW.sourceSymmetricRankExactStratum n (d + 1)
	   ```

	   Proof transcript:

	   1. From a nonzero complex regular minor obtain two checked facts already
	      in `SourceComplexChart.lean`: selected source rows are linearly
	      independent, and under `d + 1 <= n` they span the whole complex source
	      spacetime.
	   2. Prove linear independence of the selected Gram rows.  Let
	      `coeff : Fin (min n (d+1)) -> ℂ` and assume
	      `sum a, coeff a • (fun j => Gram (I a) j) = 0`.  Put
	      `w = sum a, coeff a • z (I a)`.  Evaluating the row relation at
	      selected columns `I b`, and rewriting
	      `sourceMinkowskiGram_apply_eq_complexInner`, gives
	      `sourceComplexMinkowskiInner d w (z (I b)) = 0` for every `b`.
	   3. Since the selected source rows span top, apply
	      `sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family` to
	      get `w = 0`.  The selected source-row linear independence then forces
	      every coefficient to vanish.  This proves the selected Gram rows are
	      linearly independent in `Fin n -> ℂ`.
	   4. Let `R : Matrix (Fin (min n (d+1))) (Fin n) ℂ` be the selected-row
	      submatrix of the Gram matrix.  Its rows are linearly independent, so
	      `R.rank = min n (d+1)`.  The checked `Matrix.rank_submatrix_le`
	      comparison gives `R.rank <= Gram.rank`, and `Nat.min_eq_right hD`
	      rewrites the lower bound to `d + 1`.
	   5. For a regular source point, use
	      `exists_nonzero_minor_of_sourceComplexGramRegularAt` and the previous
	      rank lower bound.
	   6. The Gram matrix belongs to the source complex Gram variety by
	      definition (`Set.range (sourceMinkowskiGram d n)`), and
	      `sourceComplexGramVariety_eq_rank_le` gives the rank upper bound
	      `rank <= d + 1` plus symmetry.  Combine upper and lower bounds by
	      antisymmetry to obtain membership in
	      `sourceSymmetricRankExactStratum n (d+1)`.

	   The next packet should combine this rank-exact bridge with
	   `dense_sourceComplexGramRegularAt` and continuity of the Gram map to get
	   density of the regular rank stratum in the source complex Gram variety,
	   without reverting to the forbidden source-space pullback shortcut for the
	   analytic identity theorem.
	0q. prove density of the regular rank-`d+1` stratum inside the source
	    complex Gram variety in the hard Hall-Wightman range `d + 1 <= n`.
	    This is a legitimate continuous-image density statement, not an
	    analytic-continuation argument: it only proves that the regular stratum
	    is dense in the scalar-product variety.  The later identity theorem must
	    still use the rank-stratum chart, lower-rank codimension, local
	    irreducibility/normality, and continuity across the singular locus.

	   ```lean
	   theorem BHW.sourceComplexGramVariety_subset_closure_sourceSymmetricRankExactStratum
	       (d n : Nat)
	       (hD : d + 1 <= n) :
	       BHW.sourceComplexGramVariety d n ⊆
	         closure (BHW.sourceSymmetricRankExactStratum n (d + 1))

	   theorem BHW.closure_sourceSymmetricRankExactStratum_eq_sourceComplexGramVariety
	       (d n : Nat)
	       (hD : d + 1 <= n) :
	       closure (BHW.sourceSymmetricRankExactStratum n (d + 1)) =
	         BHW.sourceComplexGramVariety d n
	   ```

	   Proof transcript:

	   1. Let `G ∈ sourceComplexGramVariety d n`; by definition choose a source
	      configuration `z` with `sourceMinkowskiGram d n z = G`.
	   2. To prove `G` lies in the ambient closure of the rank-exact stratum,
	      use `mem_closure_iff`.  For an open neighborhood `O` of `G`, the
	      preimage `(sourceMinkowskiGram d n) ⁻¹' O` is open by
	      `(contDiff_sourceMinkowskiGram d n).continuous` and contains `z`.
	   3. The checked dense-source theorem `dense_sourceComplexGramRegularAt`
	      gives a regular source point `z'` in that preimage.
	   4. By packet 0p,
	      `sourceMinkowskiGram d n z' ∈
	       sourceSymmetricRankExactStratum n (d+1)`, and it also lies in `O`.
	      Hence every open neighborhood of `G` meets the rank-exact stratum.
	   5. The reverse closure inclusion follows from the checked closedness of
	      `sourceComplexGramVariety d n` and the checked inclusion
	      `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety`
	      with `r = d + 1`.

	   This packet supplies the density side of the singular-locus argument.
	   It does not prove the global Hall-Wightman identity principle by itself:
	   the remaining proof-doc work must still pin the ordinary identity theorem
	   on the connected regular rank stratum and the continuity extension from
	   the lower-rank singular locus.
	0r. expose the nonempty-relative-open regular-point corollary.  This is the
	    form needed by the later identity theorem: every nonempty relatively open
	    subset of the source complex Gram variety meets the regular rank stratum.

	   ```lean
	   theorem BHW.sourceComplexGramVariety_relOpen_inter_rankExact_nonempty
	       (d n : Nat)
	       (hD : d + 1 <= n)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hU_nonempty : U.Nonempty) :
	       (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)).Nonempty
	   ```

	   Proof transcript:

	   1. Write relative openness as `U = U0 ∩ sourceComplexGramVariety d n`
	      with `U0` ambient-open.
	   2. Pick `G ∈ U`; then `G ∈ sourceComplexGramVariety d n`.
	   3. By packet 0q, `G` lies in the closure of the rank-exact stratum.
	      Applying `mem_closure_iff` to the open neighborhood `U0` gives a point
	      `G' ∈ U0 ∩ sourceSymmetricRankExactStratum n (d+1)`.
	   4. The checked inclusion
	      `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety`
	      puts `G'` back in the source complex Gram variety, hence in
	      `U = U0 ∩ sourceComplexGramVariety d n`.

	   This is the precise replacement for any vague "singular locus has no
	   interior" language at the next consumer.  It gives the regular point
	   without claiming that the analytic identity theorem has already been
	   proved.
	0s. strengthen the relative-open regular-point corollary to relative
	    density.  The final continuity step needs more than a single regular
	    point: for every relatively open source-variety domain `U`, every point
	    of `U` must lie in the ambient closure of
	    `U ∩ sourceSymmetricRankExactStratum n (d+1)`.

	   ```lean
	   theorem BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_rankExact
	       (d n : Nat)
	       (hD : d + 1 <= n)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U) :
	       U ⊆ closure
	         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
	   ```

	   Proof transcript:

	   1. Write `U = U0 ∩ sourceComplexGramVariety d n` with `U0`
	      ambient-open.
	   2. Fix `G ∈ U` and an arbitrary ambient open neighborhood `O` of `G`.
	      Then `O ∩ U0` is an ambient open neighborhood of `G`.
	   3. Since `G ∈ sourceComplexGramVariety d n`, packet 0q gives
	      `G ∈ closure (sourceSymmetricRankExactStratum n (d+1))`.
	   4. Apply `mem_closure_iff` to `O ∩ U0`; obtain
	      `G' ∈ O ∩ U0 ∩ sourceSymmetricRankExactStratum n (d+1)`.
	   5. The checked inclusion
	      `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety`
	      puts `G'` back in `sourceComplexGramVariety d n`, so
	      `G' ∈ O ∩ (U ∩ sourceSymmetricRankExactStratum n (d+1))`.

	   This is the precise density statement used later for extension from the
	   regular rank stratum to all of `U`.
	0t. prove the pure topological continuity extension from the dense regular
	    stratum.  Once the analytic part has proved that a scalar-product
	    representative vanishes on `U_reg :=
	    U ∩ sourceSymmetricRankExactStratum n (d+1)`, continuity on `U` is
	    enough to extend the equality across lower-rank points.

	   ```lean
	   theorem BHW.sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact
	       (d n : Nat)
	       (hD : d + 1 <= n)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
	       (hH_cont : ContinuousOn H U)
	       (hzero :
	         Set.EqOn H 0
	           (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))) :
	       Set.EqOn H 0 U
	   ```

	   Proof transcript:

	   1. Let `G ∈ U`.  By 0s, `G` is in the closure of `U_reg`.
	   2. Suppose `H G ≠ 0`.  The target set `{w : ℂ | w ≠ 0}` is open and
	      contains `H G`.
	   3. Use `continuousOn_iff` for `hH_cont` at `G ∈ U` to find an ambient open
	      neighborhood `O` of `G` such that every point of `O ∩ U` maps into
	      `{w | w ≠ 0}`.
	   4. Since `G ∈ closure U_reg`, choose `G' ∈ O ∩ U_reg`.
	   5. The preimage property gives `H G' ≠ 0`, while `hzero` on `U_reg`
	      gives `H G' = 0`, contradiction.  Hence `H G = 0`.

	   This is only the singular-locus continuity extension.  It deliberately
	   does not claim the analytic identity theorem on the regular rank stratum;
	   that remains the next genuine Hall-Wightman analytic-content packet.
	0u. expose continuity of local-ambient source-variety holomorphic
	    representatives.  This is needed so packet 0t can be applied directly to
	    functions satisfying the production `SourceVarietyHolomorphicOn`
	    hypothesis.

	   ```lean
	   theorem BHW.SourceVarietyHolomorphicOn.continuousOn
	       (d n : Nat)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
	       (hH : BHW.SourceVarietyHolomorphicOn d n H U) :
	       ContinuousOn H U
	   ```

	   Proof transcript:

	   1. Use `continuousOn_iff`.  Fix `Z ∈ U`, an open target set `T`, and
	      `H Z ∈ T`.
	   2. From `SourceVarietyHolomorphicOn`, choose an ambient open neighborhood
	      `U0` of `Z` on which `H` is complex differentiable.
	   3. `DifferentiableOn.continuousOn` on `U0` gives an ambient open
	      neighborhood `V` of `Z` such that `V ∩ U0` maps into `T`.
	   4. Use the open neighborhood `V ∩ U0` for continuity on `U`; any point in
	      `(V ∩ U0) ∩ U` is in `V ∩ U0`, so it maps into `T`.

	   This theorem is definition-unfolding, but it is not a wrapper: it exposes
	   the exact topological consequence of the local-ambient holomorphic
	   representative notion used in the theorem-2 API.

	   Packets 0s--0u are now checked in Lean:
	   `sourceComplexGramVariety_relOpen_subset_closure_inter_rankExact` and
	   `sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact` live in
	   `BHWPermutation/SourceComplexDensity.lean`, while
	   `SourceVarietyHolomorphicOn.continuousOn` lives next to the
	   `SourceVarietyHolomorphicOn` definition in `SourceExtension.lean`.
	   The remaining hard analytic-content packet is the regular-stratum
	   identity theorem: prove zero on
	   `U ∩ sourceSymmetricRankExactStratum n (d+1)` from a nonempty relatively
	   open zero set, using the Schur graph charts, codimension/local
	   irreducibility, and ordinary SCV identity theorem on connected regular
	   rank-stratum components.
	0v. pin the remaining regular-rank-stratum identity theorem.  This is the
	    next genuine Hall-Wightman analytic-content packet, and it is not yet
	    discharged by the density/continuity lemmas above.  Split the theorem by
	    arity:

	    * if `n <= d + 1`, the source complex Gram variety is the full symmetric
	      matrix space.  Transport to symmetric-coordinate affine space and use
	      the ordinary SCV identity theorem directly on the connected relatively
	      open domain;
	    * if `d + 1 < n`, the source complex Gram variety is the singular
	      symmetric determinantal variety.  The rank-`d+1` stratum is its regular
	      locus, covered by the checked rectangular Schur graph charts.  The
	      remaining work is to prove identity propagation on this connected
	      regular locus and then invoke packet 0t for the singular extension.

	   The hard-case theorem surface should be:

	   ```lean
	   theorem BHW.sourceComplexGramVariety_rankExact_identity_principle
	       (d n : Nat)
	       (hD : d + 1 < n)
	       {U W : Set (Fin n -> Fin n -> ℂ)}
	       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hU_conn : IsConnected U)
	       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
	       (hW_ne : W.Nonempty)
	       (hW_sub : W ⊆ U)
	       (hH : BHW.SourceVarietyHolomorphicOn d n H U)
	       (hW_zero : Set.EqOn H 0 W) :
	       Set.EqOn H 0
	         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
	   ```

	   Required internal theorem surfaces:

	   ```lean
	   def BHW.IsRelOpenInRankExactDomain
	       (d n : Nat)
	       (U V : Set (Fin n -> Fin n -> ℂ)) : Prop :=
	     ∃ V0 : Set (Fin n -> Fin n -> ℂ),
	       IsOpen V0 ∧
	         V = V0 ∩
	           (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))

	   theorem BHW.sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
	       (d n : Nat)
	       (hD : d + 1 < n)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hU_conn : IsConnected U) :
	       IsConnected
	         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))

	   theorem BHW.sourceComplexGramVariety_rankExact_local_identity
	       (d n : Nat)
	       (hD : d + 1 < n)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hH : BHW.SourceVarietyHolomorphicOn d n H U)
	       {Z0 : Fin n -> Fin n -> ℂ}
	       (hZ0 : Z0 ∈
	         U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
	       {O : Set (Fin n -> Fin n -> ℂ)}
	       (hO_rel : BHW.IsRelOpenInRankExactDomain d n U O)
	       (hO_zero : Set.EqOn H 0 O) :
	       ∃ V : Set (Fin n -> Fin n -> ℂ),
	         Z0 ∈ V ∧
	         BHW.IsRelOpenInRankExactDomain d n U V ∧
	         Set.EqOn H 0 V
	   ```

	   `IsRelOpenInRankExactDomain` is only a local proof-organizing predicate:
	   it records ordinary ambient-relative openness inside
	   `U ∩ rankExact`.  It should be introduced only if the implementation
	   genuinely needs the shorthand; otherwise inline the existential
	   definition and avoid adding a wrapper.

	   Hard-case proof transcript:

	   1. Define
	      `U_reg := U ∩ sourceSymmetricRankExactStratum n (d+1)` and
	      `W_reg := W ∩ sourceSymmetricRankExactStratum n (d+1)`.
	   2. `W_reg.Nonempty` follows from packet 0r applied to `W`, using
	      `hW_rel`, `hW_ne`, and `Nat.le_of_lt hD`.  Also
	      `W_reg ⊆ U_reg` follows from `hW_sub`.
	   3. Prove `U_reg` is connected from `hU_conn`.  This is the real
	      irreducibility/monodromy content: because
	      `sourceComplexGramVariety d n` is the symmetric rank-`<= d+1`
	      determinantal variety, because the Schur charts identify the
	      rank-exact stratum with connected graph charts, and because the
	      lower-rank locus has complex codimension
	      `n - (d+1) + 1 >= 2`, the regular locus of a connected relatively open
	      domain remains connected.  The already checked ingredients are:
	      `sourceComplexGramVariety_eq_rank_le`,
	      `exists_selected_rect_schur_chart_of_sourceComplexGramVariety_rankExact`,
	      `sourceComplexGramVariety_regularSelectedMinorPatch_relOpen`,
	      `finrank_sourceSelectedComplexSymCoordSubspace_lowerRankCodim_ge_two`,
	      and the Schur graph equations.
	   4. Let
	      `A := {Z | Z ∈ U_reg ∧ H Z = 0}`.  It is nonempty and relatively open
	      in `U_reg` because `W_reg` is a nonempty relatively open subset of
	      `U_reg` and `hW_zero` vanishes there.
	   5. Show `A` is relatively closed in `U_reg` using local Schur chart
	      identity propagation.  If `Z0 ∈ closure A ∩ U_reg`, choose a selected
	      rectangular Schur chart around `Z0`.  The chart maps a small connected
	      rank-exact neighborhood to an open subset of the finite-dimensional
	      selected-coordinate model.  Since `Z0` is in the closure of `A`, this
	      chart neighborhood contains a nonempty open subset on which `H`
	      vanishes.  Compose the local ambient representative from
	      `SourceVarietyHolomorphicOn` with the Schur chart inverse/zero-section
	      map and apply `SCV.identity_theorem_product` (or the finite-dimensional
	      affine-coordinate version) to get vanishing on the whole small chart
	      neighborhood of `Z0`; hence `Z0 ∈ A`.
	   6. Since `U_reg` is connected and `A` is nonempty, relatively open, and
	      relatively closed in `U_reg`, conclude `A = U_reg`.  This proves
	      `Set.EqOn H 0 U_reg`.
	   7. The full hard-case
	      `sourceComplexGramVariety_identity_principle` then follows by applying
	      packet 0t to extend the zero equality from `U_reg` to all of `U`,
	      using `SourceVarietyHolomorphicOn.continuousOn`.

	   This packet is the next place where implementation must focus.  It must
	   not be replaced by a source-space pullback theorem unless that theorem
	   proves the same connected regular-locus/monodromy content.

	   Implementation refinement, 2026-04-27.  The proof of this packet must use
	   the checked Schur/density declarations by their real names.  In
	   particular, do not use the informal names
	   `sourceSelectedSchurPatch`, `sourceSchurGraph_to_rank`,
	   `dense_sourceComplex_regular`, or
	   `continuous_extension_across_lowerRank`: those are not declarations in
	   the tracked Lean tree.  The checked inputs are:

	   ```lean
	   BHW.sourceSymmetricRankExactStratum_iff_reindexed_rect_schur_complement_eq_zero
	   BHW.sourceComplexGramVariety_iff_reindexed_rect_schur_complement_eq_zero
	   BHW.sourceComplexGramVariety_iff_selected_rect_schur_complement_eq_zero
	   BHW.exists_selected_rect_schur_chart_of_sourceComplexGramVariety_rankExact
	   BHW.sourceComplexGramVariety_regularSelectedMinorPatch_relOpen
	   BHW.finrank_sourceSelectedComplexSymCoordSubspace_lowerRankCodim_ge_two
	   BHW.sourceComplexGramVariety_relOpen_inter_rankExact_nonempty
	   BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_rankExact
	   BHW.sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact
	   ```

	   The strict-branch implementation is not ready if it stops at these
	   inputs.  Two genuine pieces still have to be written as Lean-ready proof
	   docs before production code should start.  After checking the actual BHW
	   infrastructure, the immediate route should use the selected complex Gram
	   chart/local-image theorems already present in the repository, not a new
	   rectangular Schur wrapper layer.  The Schur equations remain useful
	   algebraic checks; the local propagation should be built from the checked
	   source-Gram chart substrate.

	   Checked local-chart inputs:

	   ```lean
	   BHW.sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor
	   BHW.sourceComplexGramMap_localRelOpenImage_in_open_of_complexRegular
	   BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular
	   BHW.SourceVarietyHolomorphicOn.comp_sourceMinkowskiGram
	   BHW.SourceVarietyHolomorphicOn.comp_differentiableOn_chart
	   BHW.sourceMinkowskiGram_mem_rankExact_of_sourceComplexGramRegularAt
	   BHW.sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact
	   ```

	   **A. Local regular-stratum identity propagation.**  The local theorem
	   must say that if a variety-holomorphic scalar representative is already
	   zero on a relatively open subset of the regular rank stratum and a
	   regular point lies in the closure of that zero patch, then the zero set
	   contains a relatively open regular-stratum neighborhood of that point.
	   This is the local analytic-continuation step; it is not the global
	   irreducibility theorem.

	   The first bridge is that every rank-exact scalar-product matrix has a
	   complex regular source realization.  This bridge is now checked in
	   `BHWPermutation/SourceComplexDensity.lean`.  The checked direction
	   `sourceMinkowskiGram_mem_rankExact_of_sourceComplexGramRegularAt` gives
	   regular source point `->` rank-exact Gram point, and the converse is:

	   ```lean
	   theorem BHW.sourceMinkowskiGram_rank_le_sourceComplexConfigurationSpan_finrank
	       (d n : Nat)
	       (z : Fin n -> Fin (d + 1) -> ℂ) :
	       (Matrix.of fun i j : Fin n =>
	         BHW.sourceMinkowskiGram d n z i j).rank <=
	         Module.finrank ℂ (BHW.sourceComplexConfigurationSpan d n z)
	   ```

	   ```lean
	   theorem BHW.sourceSymmetricRankExactStratum_exists_complexRegular_realization
	       (d n : Nat)
	       (hD : d + 1 <= n)
	       {Z : Fin n -> Fin n -> ℂ}
	       (hZ : Z ∈ BHW.sourceSymmetricRankExactStratum n (d + 1)) :
	       ∃ z : Fin n -> Fin (d + 1) -> ℂ,
	         BHW.SourceComplexGramRegularAt d n z ∧
	         BHW.sourceMinkowskiGram d n z = Z
	   ```

	   Checked proof transcript:

	   1. Use `sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety`
	      to get a source realization `Z = sourceMinkowskiGram d n z`.
	   2. Apply the checked rank upper bound
	      `sourceMinkowskiGram_rank_le_sourceComplexConfigurationSpan_finrank`.
	   3. Since `Z` has matrix rank `d + 1`, the span dimension is at least
	      `d + 1`; the ambient dimension gives the opposite inequality, hence
	      `SourceComplexGramRegularAt d n z`.

	   The second bridge is also now checked in
	   `BHWPermutation/SourceComplexDensity.lean`.  It packages the complex
	   implicit selected-coordinate chart around a complex regular source point
	   into the exact connected source-ball image statement needed for local
	   identity propagation:

	   ```lean
	   theorem BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular
	       (d n : Nat)
	       (hD : d + 1 <= n)
	       {z0 : Fin n -> Fin (d + 1) -> ℂ}
	       (hreg : BHW.SourceComplexGramRegularAt d n z0)
	       {Vsrc : Set (Fin n -> Fin (d + 1) -> ℂ)}
	       (hVsrc_open : IsOpen Vsrc)
	       (hz0Vsrc : z0 ∈ Vsrc) :
	       ∃ Usrc : Set (Fin n -> Fin (d + 1) -> ℂ),
	         IsOpen Usrc ∧ IsConnected Usrc ∧ z0 ∈ Usrc ∧ Usrc ⊆ Vsrc ∧
	         ∃ O : Set (Fin n -> Fin n -> ℂ),
	           BHW.sourceMinkowskiGram d n z0 ∈ O ∧
	           BHW.IsRelOpenInSourceComplexGramVariety d n O ∧
	           O ⊆ BHW.sourceMinkowskiGram d n '' Usrc ∧
	           O ⊆ BHW.sourceSymmetricRankExactStratum n (d + 1) ∧
	           ∀ G ∈ O, ∃ z ∈ Usrc,
	             BHW.sourceMinkowskiGram d n z = G
	   ```

	   Checked proof transcript:

	   1. Choose a nonzero complex source minor from
	      `exists_nonzero_minor_of_sourceComplexGramRegularAt`.
	   2. Apply
	      `sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor`.
	   3. Shrink in source space to a connected metric ball contained in the
	      implicit-chart source, the same nonzero-minor patch, and `Vsrc`.
	   4. Use the open-map property of the implicit chart followed by the
	      selected-coordinate projection to construct a relatively open variety
	      neighborhood `O` of `sourceMinkowskiGram d n z0`.
	   5. The selected-coordinate uniqueness theorem
	      `sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety`
	      proves that every `G ∈ O` is the Gram matrix of a point in the
	      connected source ball.
	   6. The rank-exact image property follows because the source ball stays in
	      the complex-regular patch, so
	      `sourceMinkowskiGram_mem_rankExact_of_sourceComplexGramRegularAt`
	      applies.

	   With this checked chart packet, the local identity-propagation theorem is
	   now checked in `BHWPermutation/SourceComplexDensity.lean`:

	   ```lean
	   theorem BHW.sourceComplexGramVariety_rankExact_local_identity_near_point
	       (d n : Nat)
	       (hD : d + 1 < n)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hH : BHW.SourceVarietyHolomorphicOn d n H U)
	       {Z0 : Fin n -> Fin n -> ℂ}
	       (hZ0U : Z0 ∈ U)
	       (hZ0reg :
	         Z0 ∈ BHW.sourceSymmetricRankExactStratum n (d + 1))
	       {A : Set (Fin n -> Fin n -> ℂ)}
	       (hA_rel :
	         ∃ A0, IsOpen A0 ∧
	           A = A0 ∩
	             (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
	       (hZ0_closure : Z0 ∈ closure A)
	       (hA_zero : Set.EqOn H 0 A) :
	       ∃ V : Set (Fin n -> Fin n -> ℂ),
	         Z0 ∈ V ∧
	         (∃ V0, IsOpen V0 ∧
	           V = V0 ∩
	             (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))) ∧
	         Set.EqOn H 0 V
	   ```

	   Checked proof transcript:

	   1. Use
	      `sourceSymmetricRankExactStratum_exists_complexRegular_realization`
	      to write `Z0 = sourceMinkowskiGram d n z0` with `z0` complex regular.
	   2. Let `Vsrc := {z | sourceMinkowskiGram d n z ∈ U0}`, where
	      `U = U0 ∩ sourceComplexGramVariety d n`; this is open by
	      `contDiff_sourceMinkowskiGram`.
	   3. Apply
	      `sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`
	      at `z0` inside `Vsrc`, obtaining a connected source ball `Usrc` and a
	      relatively open rank-exact variety neighborhood `O` with
	      `O ⊆ sourceMinkowskiGram d n '' Usrc`.
	   4. Since `Z0 ∈ closure A` and `O` is a neighborhood of `Z0`, choose
	      `G1 ∈ A ∩ O`, then choose `z1 ∈ Usrc` with
	      `sourceMinkowskiGram d n z1 = G1`.
	   5. Pull `A ∩ O` back along `sourceMinkowskiGram d n`; this is an open
	      nonempty subset of the connected source ball `Usrc`.
	   6. Compose `H` with `sourceMinkowskiGram d n`.  The differentiability on
	      `Usrc` is exactly the checked helper
	      `SourceVarietyHolomorphicOn.comp_sourceMinkowskiGram`.
	   7. Apply `SCV.identity_theorem_product` on the connected source ball.
	      Then push the equality down to `O` using
	      `O ⊆ sourceMinkowskiGram d n '' Usrc`.

	   A principal-minor Schur cover is mathematically valid over `ℂ`: a complex
	   symmetric rank-`r` matrix has a nonzero principal `r × r` minor, and the
	   principal Schur graph `C = Bᵀ A⁻¹ B` is the clean Hall-Wightman chart.
	   That theorem is now checked and is used in the singular local-basis branch;
	   the selected BHW source-Gram chart infrastructure remains the checked
	   regular-rank local propagation surface.

	   **B. Connected regular-locus continuation.**  The theorem
	   `sourceComplexGramVariety_rankExact_inter_relOpen_isConnected` is not a
	   consequence of density alone.  It is the Hall-Wightman irreducibility /
	   normality content for the symmetric scalar-product determinantal variety.
	   The Lean proof may be decomposed, but the theorem surface must stay this
	   strong:

	   ```lean
	   theorem BHW.sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
	       (d n : Nat)
	       (hD : d + 1 < n)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hU_conn : IsConnected U) :
	       IsConnected
	         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
	   ```

	   Its proof must cite or prove the finite-dimensional analytic theorem:
	   in a connected relatively open subset of the irreducible normal symmetric
	   rank-`<= r` determinantal variety, removing the lower-rank singular locus
	   of complex codimension at least two leaves a connected regular locus.
	   In this repository the codimension input is already checked as
	   `finrank_sourceSelectedComplexSymCoordSubspace_lowerRankCodim_ge_two`;
	   the missing part is the analytic connectedness/normality theorem, not a
	   topology lemma about closures.

	   Finally, prove `sourceComplexGramVariety_rankExact_identity_principle`
	   from A and B:

	   ```lean
	   theorem BHW.sourceComplexGramVariety_rankExact_identity_principle
	       (d n : Nat)
	       (hD : d + 1 < n)
	       {U W : Set (Fin n -> Fin n -> ℂ)}
	       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hU_conn : IsConnected U)
	       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
	       (hW_ne : W.Nonempty)
	       (hW_sub : W ⊆ U)
	       (hH : BHW.SourceVarietyHolomorphicOn d n H U)
	       (hW_zero : Set.EqOn H 0 W) :
	       Set.EqOn H 0
	         (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
	   ```

	   Assembly transcript:

	   1. Use
	      `sourceComplexGramVariety_relOpen_inter_rankExact_nonempty` on `W`
	      to choose the initial regular zero point.  Let `A` be the relatively
	      open subset of `U ∩ rankExact` on which the zero equality has already
	      been propagated.
	   2. `A` is nonempty by the previous step.  It is relatively open by
	      construction, using
	      `sourceComplexGramVariety_rankExact_local_identity_near_point` at
	      every point already in `A`.
	   3. If `Z0 ∈ closure A ∩ U ∩ rankExact`, apply
	      `sourceComplexGramVariety_rankExact_local_identity_near_point` with
	      the same `A` and `hZ0_closure`; this proves a relatively open
	      rank-exact neighborhood of `Z0` lies in the zero set.  Hence the
	      propagated zero set is relatively closed in `U ∩ rankExact`.
	   4. `sourceComplexGramVariety_rankExact_inter_relOpen_isConnected` gives
	      connectedness of `U ∩ rankExact`; a nonempty relatively open and
	      relatively closed zero set is therefore all of `U ∩ rankExact`.
	   The full strict theorem then applies
	   `sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact` and
	   `SourceVarietyHolomorphicOn.continuousOn` to extend the identity from the
	   regular stratum to all of `U`.
	0w. prove the easy-arity algebraic reduction.  The arity split in 0v needs
	    a checked theorem saying that, when `n <= d + 1`, the source complex
	    Gram variety is the full symmetric matrix space.  This is a genuine
	    finite-dimensional rank fact, not an identity-theorem wrapper.

	   ```lean
	   theorem BHW.sourceComplexGramVariety_eq_sourceSymmetricMatrixSpace_of_le
	       (d n : Nat)
	       (hn : n <= d + 1) :
	       BHW.sourceComplexGramVariety d n =
	         BHW.sourceSymmetricMatrixSpace n
	   ```

	   Proof transcript:

	   1. Rewrite by the checked rank-defined characterization
	      `sourceComplexGramVariety_eq_rank_le`.
	   2. The forward inclusion forgets the rank bound and keeps symmetry.
	   3. For the reverse inclusion, any symmetric `Z` has
	      `(Matrix.of fun i j => Z i j).rank <= n` by `Matrix.rank_le_width`;
	      compose with `hn : n <= d + 1`.

	   This closes the algebraic part of the easy range.  The remaining easy
	   identity theorem still has to transport local ambient holomorphicity to
	   coordinates on the symmetric affine subspace before applying the ordinary
	   SCV identity theorem.
	0x. build the full symmetric affine coordinate model for the easy branch.
	    This is the coordinate infrastructure needed to make the sentence
	    "apply the ordinary SCV identity theorem on the full symmetric matrix
	    space" into Lean.  Use the selected symmetric-coordinate chart with all
	    rows selected and `I = id`.

	   Checked coordinate declarations:

	   ```lean
	   noncomputable def BHW.sourceFullSymCoordMapCLM
	       (n : Nat) :
	       (Fin
	         (Fintype.card
	           (BHW.sourceSelectedSymCoordKey n n
	             (fun i : Fin n => i))) -> ℂ) ->L[ℂ]
	         (Fin n -> Fin n -> ℂ)

	   noncomputable def BHW.sourceFullSymCoordMap
	       (n : Nat) :
	       (Fin
	         (Fintype.card
	           (BHW.sourceSelectedSymCoordKey n n
	             (fun i : Fin n => i))) -> ℂ) ->
	         (Fin n -> Fin n -> ℂ)

	   theorem BHW.sourceFullSymCoordMap_mem_sourceSymmetricMatrixSpace
	       (n : Nat)
	       (q : Fin
	         (Fintype.card
	           (BHW.sourceSelectedSymCoordKey n n
	             (fun i : Fin n => i))) -> ℂ) :
	       BHW.sourceFullSymCoordMap n q ∈
	         BHW.sourceSymmetricMatrixSpace n

	   theorem BHW.continuous_sourceFullSymCoordMap
	       (n : Nat) :
	       Continuous (BHW.sourceFullSymCoordMap n)

	   theorem BHW.differentiable_sourceFullSymCoordMap
	       (n : Nat) :
	       Differentiable ℂ (BHW.sourceFullSymCoordMap n)

	   theorem BHW.sourceFullSymCoordMap_of_mem_sourceSymmetricMatrixSpace
	       (n : Nat)
	       (Z : Fin n -> Fin n -> ℂ)
	       (hZ : Z ∈ BHW.sourceSymmetricMatrixSpace n) :
	       BHW.sourceFullSymCoordMap n
	         ((BHW.sourceSelectedComplexSymCoordFinEquiv n n
	           Function.injective_id)
	           (⟨Z, by
	             intro a b
	             exact hZ a b⟩ :
	             BHW.sourceSelectedComplexSymCoordSubspace n n
	               (fun i : Fin n => i))) = Z

	   theorem BHW.sourceFullSymCoordMap_injective
	       (n : Nat) :
	       Function.Injective (BHW.sourceFullSymCoordMap n)

	   theorem BHW.sourceSymmetricMatrixSpace_eq_range_sourceFullSymCoordMap
	       (n : Nat) :
	       BHW.sourceSymmetricMatrixSpace n =
	         Set.range (BHW.sourceFullSymCoordMap n)

	   theorem BHW.isOpen_sourceFullSymCoordMap_preimage_of_relOpen_of_le
	       (d n : Nat)
	       (hn : n <= d + 1)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U) :
	       IsOpen ((BHW.sourceFullSymCoordMap n) ⁻¹' U)

	   theorem BHW.isConnected_sourceFullSymCoordMap_preimage_of_relOpen_of_le
	       (d n : Nat)
	       (hn : n <= d + 1)
	       {U : Set (Fin n -> Fin n -> ℂ)}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hU_conn : IsConnected U) :
	       IsConnected ((BHW.sourceFullSymCoordMap n) ⁻¹' U)

	   theorem BHW.sourceComplexGramVariety_identity_principle_easy
	       (d n : Nat)
	       (hn : n <= d + 1)
	       {U W : Set (Fin n -> Fin n -> ℂ)}
	       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hU_conn : IsConnected U)
	       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
	       (hW_ne : W.Nonempty)
	       (hW_sub : W ⊆ U)
	       (hH : BHW.SourceVarietyHolomorphicOn d n H U)
	       (hW_zero : Set.EqOn H 0 W) :
	       Set.EqOn H 0 U
	   ```

	   Proof transcript:

	   1. Define `sourceFullSymCoordMapCLM n` as
	      `(sourceSelectedComplexSymCoordSubspace n n id).subtypeL` composed
	      with the inverse of the checked selected-coordinate equivalence
	      `sourceSelectedComplexSymCoordFinEquiv n n Function.injective_id`.
	   2. Its image is symmetric because membership in
	      `sourceSelectedComplexSymCoordSubspace n n id` is exactly the
	      relation `A i j = A j i`.
	   3. Continuity and differentiability are immediate from the continuous
	      linear map.
	   4. Surjectivity onto `sourceSymmetricMatrixSpace n`: for a symmetric
	      matrix `Z`, package it as
	      `A : sourceSelectedComplexSymCoordSubspace n n id`, take
	      `q := sourceSelectedComplexSymCoordFinEquiv n n Function.injective_id A`,
	      and use `ContinuousLinearEquiv.symm_apply_apply`.
	   5. Injectivity follows because equality after coercion to the ambient
	      matrix space gives equality in the selected symmetric-coordinate
	      submodule by `Subtype.ext`, and the inverse selected-coordinate
	      equivalence is injective.
	   6. If `n <= d + 1` and `U = U0 ∩ sourceComplexGramVariety d n`, rewrite
	      the variety by packet 0w.  Since every `sourceFullSymCoordMap n q`
	      is symmetric, the coordinate preimage of `U` is exactly the coordinate
	      preimage of the ambient open set `U0`, hence it is open.
	   7. For connectedness, define the inverse coordinate map on the subtype
	      `U` by packaging each `Z : U` as an element of
	      `sourceSelectedComplexSymCoordSubspace n n id`; this packaging is
	      continuous by `Continuous.subtype_mk`.  Its image of `Set.univ : Set U`
	      is exactly `sourceFullSymCoordMap n ⁻¹' U`, using the reconstruction
	      and injectivity lemmas above.  Since `hU_conn` gives
	      `ConnectedSpace U`, the image is connected.
	   8. For `sourceComplexGramVariety_identity_principle_easy`, let
	      `Γ := sourceFullSymCoordMap n`, `Ũ := Γ ⁻¹' U`, and `Ŵ := Γ ⁻¹' W`.
	      The previous checked lemmas give open connected `Ũ` and open `Ŵ`.
	   9. `Ŵ.Nonempty` follows from `hW_ne` by reconstructing a full symmetric
	      coordinate preimage of any `Z ∈ W`; `Ŵ ⊆ Ũ` follows from `hW_sub`.
	   10. `H ∘ Γ` is differentiable on `Ũ`: for each `q ∈ Ũ`, the point
	       `Γ q` lies in `U`; apply the local ambient differentiability witness
	       from `hH (Γ q)` and compose with
	       `differentiable_sourceFullSymCoordMap n`.
	   11. Choose `q0 ∈ Ŵ`.  Since `Ŵ` is open and `hW_zero` holds on `W`,
	       `fun q => H (Γ q)` is eventually equal to zero at `q0`.
	   12. Apply `SCV.identity_theorem_SCV` to `H ∘ Γ` and the zero function on
	       the connected open coordinate domain `Ũ`, then push the resulting
	       equality back to `U` using symmetric-coordinate reconstruction.

	   This checked theorem completes the easy branch without touching the singular
	   determinantal geometry.  The strict branch `d + 1 < n` remains the
	   Hall-Wightman scalar-product-variety continuation theorem from packet 0v.
	0y. final arity split for `sourceComplexGramVariety_identity_principle`.
	    The strict regular-rank theorem from packet 0v and the final arity split
	    are now checked in `BHWPermutation/SourceComplexDensity.lean`.  The
	    final theorem is the following short, non-wrapper arity split:

	   ```lean
	   theorem BHW.sourceComplexGramVariety_identity_principle
	       (d n : Nat)
	       {U W : Set (Fin n -> Fin n -> ℂ)}
	       {H : (Fin n -> Fin n -> ℂ) -> ℂ}
	       (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
	       (hU_conn : IsConnected U)
	       (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
	       (hW_ne : W.Nonempty)
	       (hW_sub : W ⊆ U)
	       (hH : BHW.SourceVarietyHolomorphicOn d n H U)
	       (hW_zero : Set.EqOn H 0 W) :
	       Set.EqOn H 0 U := by
	     by_cases hn : n <= d + 1
	     · exact
	         BHW.sourceComplexGramVariety_identity_principle_easy
	           d n hn hU_rel hU_conn hW_rel hW_ne hW_sub hH hW_zero
	     · have hD : d + 1 < n := by omega
	       have hzero_reg :
	           Set.EqOn H 0
	             (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)) :=
	         BHW.sourceComplexGramVariety_rankExact_identity_principle
	           d n hD hU_rel hU_conn hW_rel hW_ne hW_sub hH hW_zero
	       exact
	         BHW.sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact
	           d n (Nat.le_of_lt hD) hU_rel
	           (BHW.SourceVarietyHolomorphicOn.continuousOn d n hH)
	           hzero_reg
	   ```

	   This final theorem is now checked.  The easy branch uses full symmetric
	   coordinates; the strict branch uses the checked connected regular-locus
	   theorem and the checked dense rank-exact extension.  The continuity
	   extension in the last line remains the already checked final step, not an
	   additional Hall-Wightman source assumption.

Checked strict-branch continuation obligations:

1. on a patch with an invertible selected principal `r × r` block `A`, write a
   symmetric matrix as `[[A, B], [Bᵀ, C]]`;
2. show `rank([[A,B],[Bᵀ,C]]) = r + rank(C - Bᵀ A⁻¹ B)`;
3. conclude that the rank-exact `r` stratum on this patch is exactly the graph
   `C = Bᵀ A⁻¹ B`, with coordinates `(A,B)`;
4. compute `dim rankExact(r) = r*n - r*(r-1)/2`;
5. for `D = d + 1`, compute the singular codimension inside rank `≤ D`:
   `dim rankExact(D) - dim rankExact(D-1) = n - D + 1 = n - d`;
6. the singular case exists only when `D < n`, so `n - d ≥ 2`.

With local irreducibility/normality and this codimension bound, the global
identity theorem can be proved without a fully general analytic-space identity
API:

1. `U_reg := U ∩ sourceSymmetricRankExactStratum n (d + 1)` is connected and
   dense in `U`;
2. `W_reg := W ∩ U_reg` is nonempty because `W` is relatively open in `U` and
   the singular locus has empty interior in the locally irreducible variety;
3. restrict the locally ambient-holomorphic representative `H` to the connected
   complex manifold `U_reg`;
4. apply the ordinary manifold/coordinate identity theorem on `U_reg`, using
   `W_reg` as the nonempty open zero set;
5. extend zero from dense `U_reg` to all of `U` by continuity from the local
   ambient holomorphic representatives.

This route still proves the same mathematical content as analytic
irreducibility of the scalar-product variety; it just decomposes it into
rank-stratum charts, codimension, local irreducibility, and continuity.  It does
not license the source-space pullback shortcut: the audit agrees that the
pullback route needs an equivalent monodromy/quotient theorem before it can be
used.

Checked strict connectedness packet:

The connectedness theorem was not implemented as a single opaque black box.
The proof is split into the following genuine subclaims.  These are not
wrappers: each one isolates a separate mathematical ingredient in
Hall-Wightman's scalar-product variety argument.

**0z-1. Topological assembly from local connected punctured neighborhoods.**

This theorem is now checked in
`BHWPermutation/SourceComplexDensity.lean`.  It is the abstract lemma that
turns density plus local irreducibility into connectedness of the dense regular
locus.

```lean
theorem BHW.sourceComplexGramVariety_rankExact_inter_relOpen_isConnected_of_local_basis
    (d n : Nat)
    {U : Set (Fin n -> Fin n -> ℂ)}
    (hU_conn : IsConnected U)
    (hdense :
      U ⊆ closure
        (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
    (hlocal :
      ∀ Z, Z ∈ U →
        ∀ N0 : Set (Fin n -> Fin n -> ℂ), IsOpen N0 → Z ∈ N0 →
          ∃ V : Set (Fin n -> Fin n -> ℂ),
            Z ∈ V ∧
            BHW.IsRelOpenInSourceComplexGramVariety d n V ∧
            V ⊆ U ∩ N0 ∧
            IsConnected
              (V ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))) :
    IsConnected
      (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
```

Checked proof transcript:

1. Nonemptiness follows from `hU_conn.nonempty`, `hdense`, and the local basis:
   apply `hlocal` inside `Set.univ` at any point of `U`; the connected
   punctured neighborhood has a point in `U_reg`.
2. Suppose `U_reg` is separated as `A ∪ B` by disjoint nonempty relatively open
   subsets.  Equivalently, use Mathlib's
   `isPreconnected_iff_subset_of_disjoint` on `U_reg`.
3. Let `clU A := U ∩ closure A` and `clU B := U ∩ closure B`.  Density of
   `U_reg` in `U` gives `U ⊆ clU A ∪ clU B`.
4. These two relative closed subsets of `U` are nonempty.  If they were
   disjoint, they would disconnect `U`, contradicting `hU_conn`.  Hence choose
   `Z0 ∈ U ∩ closure A ∩ closure B`.
5. Apply `hlocal Z0` inside a small ambient open neighborhood `N0` contained in
   the intersection of the two ambient neighborhoods witnessing relative
   openness of the separation.  The set
   `V_reg := V ∩ sourceSymmetricRankExactStratum n (d+1)` is connected.
6. Since `Z0 ∈ closure A ∩ closure B` and `V` is a relative neighborhood of
   `Z0`, both `V_reg ∩ A` and `V_reg ∩ B` are nonempty.  They are also disjoint
   relatively open subsets whose union is `V_reg`, contradicting
   `IsConnected V_reg`.

The exact Lean proof should avoid introducing a new permanent predicate for
relative connected bases unless the term gets unwieldy; the `hlocal` hypothesis
above is explicit enough for the proof.

**0z-2. Source-variety local connected rank-exact basis.**

This is the genuine local Hall-Wightman normality/irreducibility theorem.  It
was the main finite-dimensional analytic-geometry proof needed before the
global connectedness theorem became an assembly theorem, and is now checked in
`BHWPermutation/SourceComplexDensity.lean` with its singular Schur-chart branch
checked in `BHWPermutation/SourceComplexSchurGraph.lean`.

```lean
theorem BHW.sourceComplexGramVariety_local_rankExact_connected_basis
    (d n : Nat)
    (hD : d + 1 < n)
    {Z0 : Fin n -> Fin n -> ℂ}
    (hZ0 : Z0 ∈ BHW.sourceComplexGramVariety d n)
    {N0 : Set (Fin n -> Fin n -> ℂ)}
    (hN0_open : IsOpen N0)
    (hZ0N0 : Z0 ∈ N0) :
    ∃ V : Set (Fin n -> Fin n -> ℂ),
      Z0 ∈ V ∧
      BHW.IsRelOpenInSourceComplexGramVariety d n V ∧
      V ⊆ N0 ∩ BHW.sourceComplexGramVariety d n ∧
      IsConnected
        (V ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
```

Proof transcript by rank of `Z0`:

1. Let `D := d + 1`.  Use
   `sourceComplexGramVariety_eq_rank_le` to regard `Z0` as a symmetric
   matrix of rank `k ≤ D`.
2. If `k = D`, use the checked complex-regular realization
   `sourceSymmetricRankExactStratum_exists_complexRegular_realization` and the
   checked local source-Gram chart
   `sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`.
   The existing theorem already gives a relative-open rank-exact neighborhood
   in `N0`; for the connected-basis theorem it must be strengthened by one real
   conclusion, not wrapped:

   ```lean
   theorem BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular
       (d n : Nat)
       (hD : d + 1 ≤ n)
       {z0 : Fin n -> Fin (d + 1) -> ℂ}
       (hreg : BHW.SourceComplexGramRegularAt d n z0)
       {Vsrc : Set (Fin n -> Fin (d + 1) -> ℂ)}
       (hVsrc_open : IsOpen Vsrc)
       (hz0Vsrc : z0 ∈ Vsrc) :
       ∃ U : Set (Fin n -> Fin (d + 1) -> ℂ),
         IsOpen U ∧ IsConnected U ∧ z0 ∈ U ∧ U ⊆ Vsrc ∧
         ∃ O : Set (Fin n -> Fin n -> ℂ),
           BHW.sourceMinkowskiGram d n z0 ∈ O ∧
           BHW.IsRelOpenInSourceComplexGramVariety d n O ∧
           O ⊆ BHW.sourceMinkowskiGram d n '' U ∧
           O ⊆ BHW.sourceSymmetricRankExactStratum n (d + 1) ∧
           IsConnected O ∧
           ∀ G ∈ O, ∃ z ∈ U,
             BHW.sourceMinkowskiGram d n z = G
   ```

   This strengthening is now checked directly in
   `BHWPermutation/SourceComplexDensity.lean` by reusing the body of the
   existing local chart theorem, not by introducing a parallel chart layer:
   - the implicit-chart image `T := e '' ball` is connected,
   - `R := Prod.fst '' T` is connected,
   - the produced relatively open image `O` is equal to
     `sourceMinkowskiGram d n '' U`, because the selected-coordinate chart
     gives both inclusions,
   - hence the produced `V ∩ rankExact` is connected.

   The regular branch of the local-basis theorem is now checked directly as:

   ```lean
   theorem BHW.sourceComplexGramVariety_local_rankExact_connected_basis_regular
       (d n : Nat)
       (hD : d + 1 < n)
       {Z0 : Fin n -> Fin n -> ℂ}
       (hZ0reg : Z0 ∈ BHW.sourceSymmetricRankExactStratum n (d + 1))
       {N0 : Set (Fin n -> Fin n -> ℂ)}
       (hN0_open : IsOpen N0)
       (hZ0N0 : Z0 ∈ N0) :
       ∃ V : Set (Fin n -> Fin n -> ℂ),
         Z0 ∈ V ∧
         BHW.IsRelOpenInSourceComplexGramVariety d n V ∧
         V ⊆ N0 ∩ BHW.sourceComplexGramVariety d n ∧
         IsConnected
           (V ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
   ```

   Proof: choose the checked complex-regular realization of `Z0`; apply
   `sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular`
   to the source preimage of `N0`; take the produced `O` as `V`.  The theorem's
   `O ⊆ rankExact` turns `V ∩ rankExact` into `V`, and the surjectivity field
   plus `U ⊆ {z | sourceMinkowskiGram d n z ∈ N0}` proves `V ⊆ N0`.
3. If `k < D`, choose a nonzero principal `k × k` minor.  For `k = 0`, this is
   the zero block case.  After reindexing, write a nearby symmetric matrix as
   `[[A, B], [Bᵀ, C]]` with `A` invertible.  The existing file
   `SourceComplexSchurPatch.lean` proves the zero-Schur special case
   `rank_eq_card_iff_reindexed_schur_complement_eq_zero`, but that is not
   enough for singular points.  The singular proof needs the stronger rank
   additivity/product chart below.

   This algebraic theorem is now checked in
   `BHWPermutation/SourceComplexSchurPatch.lean`:

   ```lean
   theorem BHW.rank_reindexed_principal_eq_card_add_rank_schur
       {ι r q : Type*} [Fintype ι] [Fintype r] [Fintype q]
       [DecidableEq ι] [DecidableEq r] [DecidableEq q]
       (Z : Matrix ι ι ℂ)
       (e : ι ≃ r ⊕ q)
       (hA : IsUnit ((Z.reindex e e).toBlocks₁₁.det)) :
       Z.rank =
         Fintype.card r +
           ((Z.reindex e e).toBlocks₂₂ -
             (Z.reindex e e).toBlocks₂₁ *
               (Z.reindex e e).toBlocks₁₁⁻¹ *
               (Z.reindex e e).toBlocks₁₂).rank
   ```

   Its proof is ordinary finite-dimensional Gaussian block elimination: first
   prove block-diagonal rank additivity, then apply Mathlib's Schur LDU
   factorization and rank invariance under multiplication by determinant-unit
   triangular block matrices.

   The source-rank consequences are also checked there in direct rank form,
   avoiding an artificial coordinate wrapper for the complement index type:

   ```lean
   theorem BHW.sourceSymmetricRankLEVariety_iff_principal_schur_rank_le
       (n D : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {Z : Fin n -> Fin n -> ℂ}
       (hA : IsUnit
         (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁.det))
       (hrD : Fintype.card r ≤ D) :
       Z ∈ BHW.sourceSymmetricRankLEVariety n D ↔
         Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
         (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₂₂ -
             ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₂₁ *
               ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁⁻¹ *
               ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂).rank
           ≤ D - Fintype.card r

   theorem BHW.sourceSymmetricRankExactStratum_iff_principal_schur_rank_eq
       (n D : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {Z : Fin n -> Fin n -> ℂ}
       (hA : IsUnit
         (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁.det))
       (hrD : Fintype.card r ≤ D) :
       Z ∈ BHW.sourceSymmetricRankExactStratum n D ↔
         Z ∈ BHW.sourceSymmetricMatrixSpace n ∧
         (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₂₂ -
             ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₂₁ *
               ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁⁻¹ *
               ((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂).rank
           = D - Fintype.card r
   ```

   With these statements, the local product chart is explicit:
   `rank≤D near Z0` is locally the product of connected invertible `(A,B)`
   coordinates and the cone of symmetric matrices `S` with
   `rank S ≤ D-k`, where `S = C - Bᵀ A⁻¹ B`; the rank-exact locus corresponds
   to `rank S = D-k`.

4. Prove the cone lemma used in the singular case:

   ```lean
   theorem BHW.sourceSymmetricRankExactCone_small_connected
       (m r : Nat)
       (hr : r ≤ m)
       {N : Set (Fin m -> Fin m -> ℂ)}
       (hN_open : IsOpen N)
       (h0N : (0 : Fin m -> Fin m -> ℂ) ∈ N) :
       ∃ C : Set (Fin m -> Fin m -> ℂ),
         (0 : Fin m -> Fin m -> ℂ) ∈ C ∧
         IsOpen C ∧ C ⊆ N ∧
         IsConnected (C ∩ BHW.sourceSymmetricRankExactStratum m r)
   ```

   Its proof is not a density argument.  The Lean implementation should split
   it into the following genuine finite-dimensional lemmas, in this order.

   First record the cone algebra:

   ```lean
   theorem BHW.matrix_rank_smul_of_ne_zero
       {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
       (c : ℂ) (hc : c ≠ 0) (A : Matrix m n ℂ) :
       (c • A).rank = A.rank

   theorem BHW.sourceSymmetricRankExactStratum_smul_mem
       {n r : Nat} {Z : Fin n -> Fin n -> ℂ}
       (hZ : Z ∈ BHW.sourceSymmetricRankExactStratum n r)
       {c : ℂ} (hc : c ≠ 0) :
       (c • Z) ∈ BHW.sourceSymmetricRankExactStratum n r

   theorem BHW.sourceComplexDotGram_smul
       (D n : Nat) (a : ℂ) (z : Fin n -> Fin D -> ℂ) :
       BHW.sourceComplexDotGram D n (a • z) =
         (a * a) • BHW.sourceComplexDotGram D n z

   theorem BHW.sourceComplexDotGram_smul_sqrt
       (D n : Nat) (c : ℂ) (z : Fin n -> Fin D -> ℂ) :
       BHW.sourceComplexDotGram D n
           ((BHW.complexSquareRootChoice c) • z) =
         c • BHW.sourceComplexDotGram D n z
   ```

   These cone-scaling lemmas are now checked in
   `BHWPermutation/SourceComplexCone.lean`.  They are not wrappers: the first
   lemma says nonzero scalar multiplication is an invertible linear change of
   rows, the second is the exact-rank cone property, and the last two align the
   cone operation with the ordinary complex dot-Gram parametrization used by
   Hall-Wightman.

   Next introduce the actual parametrizing space, without hiding it in a new
   opaque predicate:

   ```lean
   def BHW.sourceFullRankConfigurations (m r : Nat) :
       Set (Fin m -> Fin r -> ℂ) :=
     {A |
       (Matrix.of fun i a : Fin m => A i a).rank = r}

   theorem BHW.sourceComplexDotGram_mem_rankExact_of_fullRank
       {m r : Nat} {A : Fin m -> Fin r -> ℂ}
       (hA :
         (Matrix.of fun i a : Fin m => A i a).rank = r) :
       BHW.sourceComplexDotGram r m A ∈
         BHW.sourceSymmetricRankExactStratum m r

   theorem BHW.exists_fullRank_sourceComplexDotGram_of_rankExact
       {m r : Nat} {Z : Fin m -> Fin m -> ℂ}
       (hZ : Z ∈ BHW.sourceSymmetricRankExactStratum m r) :
       ∃ A : Fin m -> Fin r -> ℂ,
         A ∈ BHW.sourceFullRankConfigurations m r ∧
           BHW.sourceComplexDotGram r m A = Z
   ```

   The first theorem uses
   `rank(A * Aᵀ) = rank A` when `A` has full column rank; the second is the
   checked complex symmetric rank factorization upgraded from rank `≤ r` to
   exact rank `r`.  Both parametrization lemmas are now checked in
   `BHWPermutation/SourceComplexCone.lean`.

   Then prove path-connectedness of the full-rank configuration space:

   ```lean
   theorem BHW.sourceFullRankConfigurations_isPathConnected
       (m r : Nat) (hr : r ≤ m) :
       IsPathConnected (BHW.sourceFullRankConfigurations m r)
   ```

   The preferred proof should be constructive enough for Lean:

   ```lean
   def BHW.standardFullRankConfiguration
       (m r : Nat) (hr : r ≤ m) : Fin m -> Fin r -> ℂ :=
     fun i a => if i = Fin.castLE hr a then 1 else 0

   def BHW.selectedFullRankFrame
       {m r : Nat} (I : Fin r -> Fin m) :
       Fin m -> Fin r -> ℂ :=
     fun i a => if i = I a then 1 else 0

   theorem BHW.sourceFullRankConfigurations_joined_selectedFrame
       {m r : Nat} {A : Fin m -> Fin r -> ℂ}
       (hA : A ∈ BHW.sourceFullRankConfigurations m r)
       {I : Fin r -> Fin m}
       (hIminor :
         Matrix.det (fun a b : Fin r => A (I a) b) ≠ 0) :
       JoinedIn (BHW.sourceFullRankConfigurations m r)
         A (BHW.selectedFullRankFrame I)

   theorem BHW.exists_sourceFullRankConfiguration_selected_minor_ne_zero
       {m r : Nat} {A : Fin m -> Fin r -> ℂ}
       (hA : A ∈ BHW.sourceFullRankConfigurations m r) :
       ∃ I : Fin r -> Fin m, Function.Injective I ∧
         Matrix.det (fun a b : Fin r => A (I a) b) ≠ 0

   theorem BHW.selectedFullRankFrame_joined_standard
       {m r : Nat} (hr : r ≤ m)
       {I : Fin r -> Fin m} (hI : Function.Injective I) :
       JoinedIn (BHW.sourceFullRankConfigurations m r)
         (BHW.selectedFullRankFrame I)
         (BHW.standardFullRankConfiguration m r hr)
   ```

   The definitions `sourceFullRankConfigurations`,
   `selectedFullRankFrame`, `standardFullRankConfiguration`, and the endpoint
   membership lemmas
   `selectedFullRankFrame_mem_sourceFullRankConfigurations` and
   `standardFullRankConfiguration_mem_sourceFullRankConfigurations` are now
   checked in `BHWPermutation/SourceComplexCone.lean`.  The same file also
   checks the two action invariance lemmas
   `sourceFullRankConfigurations_left_mul_isUnit_mem` and
   `sourceFullRankConfigurations_right_mul_isUnit_mem`, which are the algebraic
   facts used when pushing `GL_m(ℂ)` and `GL_r(ℂ)` paths into full-rank
   configuration paths.  The path-level versions
   `sourceFullRankConfigurations_joined_left_mul_GL` and
   `sourceFullRankConfigurations_joined_right_mul_GL` are now checked too.

   The first theorem is now checked exactly as planned.  In the selected-minor
   chart, put `B = (A (I a) b)`.  The path first right-multiplies `A` through
   `GL_r(ℂ)` from `1` to `B⁻¹`, so the selected block becomes the identity.
   It then linearly contracts all remaining rows to zero; every intermediate
   matrix stays full rank because the selected block is still the identity.
   The existence lemma above extracts a selected nonzero row minor from any
   full-rank configuration by applying
   `exists_nondegenerate_square_submatrix_of_rank_ge` and absorbing the column
   permutation into the determinant.

   The second theorem is also checked.  Mathlib's
   `Equiv.Perm.isMultiplyPretransitive` extends the injection
   `I : Fin r -> Fin m` to a permutation carrying the standard rows to the
   selected rows.  The associated permutation matrix is a point of `GL_m(ℂ)`;
   applying the checked left-`GL` path to the standard frame gives a path to
   the selected frame, and reversing it gives the stated orientation.  This is
   the honest Stiefel-space argument; do not replace it by a Schur-chart
   wrapper.

   Combining the parametrization and continuity of `sourceComplexDotGram`
   gives:

   ```lean
   theorem BHW.continuous_sourceComplexDotGram
       (D n : Nat) :
       Continuous (BHW.sourceComplexDotGram D n)

   theorem BHW.sourceSymmetricRankExactStratum_eq_sourceComplexDotGram_image_fullRank
       (m r : Nat) :
       BHW.sourceSymmetricRankExactStratum m r =
         BHW.sourceComplexDotGram r m ''
           BHW.sourceFullRankConfigurations m r

   theorem BHW.sourceSymmetricRankExactStratum_isPathConnected_of_fullRank
       (m r : Nat)
       (hfull :
         IsPathConnected (BHW.sourceFullRankConfigurations m r)) :
       IsPathConnected
         (BHW.sourceSymmetricRankExactStratum m r)

   theorem BHW.sourceSymmetricRankExactStratum_isPathConnected
       (m r : Nat) (hr : r ≤ m) :
       IsPathConnected
         (BHW.sourceSymmetricRankExactStratum m r)
   ```

   All four theorems in this block are now checked in
   `BHWPermutation/SourceComplexCone.lean`.  The full Stiefel-space
   path-connectedness theorem is no longer a blocker.

   The radial endpoints, compact-bound middle segment, and small-cone
   assembly are now checked as well:

   ```lean
   theorem BHW.sourceSymmetricRankExactStratum_joined_radial_smul
       {m r : Nat} {Z : Fin m -> Fin m -> ℂ}
       (hZ : Z ∈ BHW.sourceSymmetricRankExactStratum m r)
       {ρ : ℝ} (hρ : 0 < ρ) :
       JoinedIn (BHW.sourceSymmetricRankExactStratum m r)
         Z ((ρ : ℂ) • Z)

   theorem BHW.sourceSymmetricRankExactStratum_joined_ball_radial_smul
       {m r : Nat} {ε ρ : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ 1)
       {Z : Fin m -> Fin m -> ℂ}
       (hZball : Z ∈ Metric.ball (0 : Fin m -> Fin m -> ℂ) ε)
       (hZ : Z ∈ BHW.sourceSymmetricRankExactStratum m r) :
       JoinedIn
         (Metric.ball (0 : Fin m -> Fin m -> ℂ) ε ∩
           BHW.sourceSymmetricRankExactStratum m r)
         Z ((ρ : ℂ) • Z)

   theorem BHW.exists_pos_norm_bound_of_path
       {E : Type*} [NormedAddCommGroup E]
       {X Y : E} (γ : Path X Y) :
       ∃ M : ℝ, 0 < M ∧ ∀ t : unitInterval, ‖γ t‖ ≤ M

   theorem BHW.sourceSymmetricRankExactStratum_joined_ball_scaled_path
       {m r : Nat} {ε ρ M : ℝ} (hρ : 0 < ρ)
       {X Y : Fin m -> Fin m -> ℂ} (γ : Path X Y)
       (hγ : ∀ t : unitInterval,
         γ t ∈ BHW.sourceSymmetricRankExactStratum m r)
       (hbound : ∀ t : unitInterval, ‖γ t‖ ≤ M)
       (hρM : ρ * M < ε) :
       JoinedIn
         (Metric.ball (0 : Fin m -> Fin m -> ℂ) ε ∩
           BHW.sourceSymmetricRankExactStratum m r)
         ((ρ : ℂ) • X) ((ρ : ℂ) • Y)

   theorem BHW.sourceSymmetricRankExactStratum_ball_isPathConnected
       (m r : Nat) (hr : r ≤ m) {ε : ℝ} (hε : 0 < ε) :
       IsPathConnected
         (Metric.ball (0 : Fin m -> Fin m -> ℂ) ε ∩
           BHW.sourceSymmetricRankExactStratum m r)

   theorem BHW.sourceSymmetricRankExactCone_small_connected
       (m r : Nat) (hr : r ≤ m)
       {N : Set (Fin m -> Fin m -> ℂ)}
       (hN_open : IsOpen N)
       (h0N : (0 : Fin m -> Fin m -> ℂ) ∈ N) :
       ∃ C : Set (Fin m -> Fin m -> ℂ),
         (0 : Fin m -> Fin m -> ℂ) ∈ C ∧
         IsOpen C ∧ C ⊆ N ∧
         IsConnected (C ∩ BHW.sourceSymmetricRankExactStratum m r)
   ```

   The proof chooses `ε > 0` with `Metric.ball 0 ε ⊆ N` and puts
   `C := Metric.ball 0 ε`.  For two points `X,Y ∈ C ∩ rankExact`, it takes a
   path `γ` in the rank-exact stratum from `X` to `Y`.  Compactness of
   `γ '' Set.univ` gives a positive finite bound `M`; `exists_pos_mul_lt`
   chooses `δ > 0` with `δ * M < ε`, and Lean uses
   `ρ := min δ 1` so both `0 < ρ ≤ 1` and `ρ * M < ε`.  The concatenated path

   1. radial path from `X` to `ρ • X`,
   2. scaled path `t ↦ ρ • γ t`,
   3. radial path from `ρ • Y` to `Y`,

   stays in `C ∩ rankExact` because all radial scalars are nonzero and the
   exact stratum is a cone.  This gives path-connectedness, hence connectedness
   of `C ∩ rankExact`.  This completes the cone lemma; no Schur-chart or
   rank-exact connectedness black box remains at this layer.

5. Implemented singular Schur product chart, not another zero-Schur wrapper.
   This was the remaining local-basis proof step.  The chart lives in the small
   companion layer `SourceComplexSchurGraph.lean` over
   `SourceComplexSchurPatch.lean` and `SourceComplexCone.lean`, because
   `SourceComplexSchurPatch.lean` is already a large checked algebra file.  The
   implementation exposes the actual graph map as a definition, then proves the
   rank-exact preimage theorem that makes the connected-cone input usable.

   The following definition is now checked in
   `BHWPermutation/SourceComplexSchurGraph.lean`, with the transpose convention
   matching the symmetric source scalar-product matrices in the checked
   principal Schur rank theorem:

   ```lean
   noncomputable def BHW.sourcePrincipalSchurGraph
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
       Fin n -> Fin n -> ℂ :=
     fun i j =>
       (Matrix.fromBlocks A B Bᵀ (S + Bᵀ * A⁻¹ * B))
         (e i) (e j)
   ```

   The block-recovery lemmas are the first Lean target.  They should be proved
   by extensionality and `simp [sourcePrincipalSchurGraph]`; keep them small so
   the later rank theorem does not repeatedly unfold the whole graph.

   ```lean
   theorem BHW.sourcePrincipalSchurGraph_toBlocks₁₁
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
       ((Matrix.of fun i j : Fin n =>
           BHW.sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₁₁ = A

   theorem BHW.sourcePrincipalSchurGraph_toBlocks₁₂
       ... :
       ((Matrix.of fun i j : Fin n =>
           BHW.sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₁₂ = B

   theorem BHW.sourcePrincipalSchurGraph_toBlocks₂₁
       ... :
       ((Matrix.of fun i j : Fin n =>
           BHW.sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₂₁ = Bᵀ

   theorem BHW.sourcePrincipalSchurGraph_schurComplement
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
       ((Matrix.of fun i j : Fin n =>
           BHW.sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₂₂ -
         ((Matrix.of fun i j : Fin n =>
           BHW.sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₂₁ *
           ((Matrix.of fun i j : Fin n =>
             BHW.sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₁₁⁻¹ *
           ((Matrix.of fun i j : Fin n =>
             BHW.sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₁₂ = S
   ```

   All four block-recovery lemmas and this Schur-complement recovery lemma are
   checked in `SourceComplexSchurGraph.lean`.  In the last proof, after the
   block-recovery rewrites the target is
   `(S + Bᵀ * A⁻¹ * B) - Bᵀ * A⁻¹ * B = S`.  Use the field/ring simp after
   rewriting with the recovered blocks; do not unfold the graph inside the
   rank theorem.

   The inverse-coordinate direction of the same chart is now checked as well:

   ```lean
   theorem BHW.matrix_eq_zero_of_rank_eq_zero
       {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
       (A : Matrix m n ℂ) (hA : A.rank = 0) : A = 0

   theorem BHW.sourcePrincipalSchurGraph_coordinates_eq_of_symmetric
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {Z : Matrix (Fin n) (Fin n) ℂ}
       (hZsym : Zᵀ = Z) :
       (Matrix.of fun i j : Fin n =>
         BHW.sourcePrincipalSchurGraph n e
           ((Z.reindex e e).toBlocks₁₁)
           ((Z.reindex e e).toBlocks₁₂)
           (BHW.reindexedRectSchurComplement Z e e) i j) = Z
   ```

   The rank-zero lemma is the finite-dimensional linear algebra fact used below
   to convert the singular basepoint Schur complement from rank zero to the
   zero matrix.  The graph inverse is the algebraic equality needed in the final
   singular chart: a
   symmetric matrix on the determinant patch is recovered from its `(A,B,S)`
   Schur coordinates.  The proof reindexes `Z` to `M`, derives
   `M.toBlocks₂₁ = M.toBlocks₁₂ᵀ` from symmetry, rewrites
   `S + BᵀA⁻¹B = C`, and then checks the four block cases.  It is not a wrapper
   around the local-basis theorem.

   The coordinate symmetry facts needed to land in the product factors are also
   checked:

   ```lean
   theorem BHW.principalBlock_transpose_eq_of_symmetric
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {Z : Matrix (Fin n) (Fin n) ℂ}
       (hZsym : Zᵀ = Z) :
       ((Z.reindex e e).toBlocks₁₁)ᵀ =
         (Z.reindex e e).toBlocks₁₁

   theorem BHW.reindexedRectSchurComplement_transpose_eq_of_symmetric
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {Z : Matrix (Fin n) (Fin n) ℂ}
       (hZsym : Zᵀ = Z) :
       (BHW.reindexedRectSchurComplement Z e e)ᵀ =
         BHW.reindexedRectSchurComplement Z e e
   ```

   Symmetry and source-rank membership then become direct consumers:

   ```lean
   theorem BHW.sourcePrincipalSchurGraph_mem_symmetric
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {A : Matrix r r ℂ} {S : Matrix q q ℂ} (B : Matrix r q ℂ)
       (hA_sym : Aᵀ = A) (hS_sym : Sᵀ = S) :
       BHW.sourcePrincipalSchurGraph n e A B S ∈
         BHW.sourceSymmetricMatrixSpace n

   theorem BHW.sourcePrincipalSchurGraph_mem_rankLE_iff
       (n D : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {A : Matrix r r ℂ} (hA_unit : IsUnit A.det)
       (hA_sym : Aᵀ = A)
       {B : Matrix r q ℂ} {S : Matrix q q ℂ}
       (hS_sym : Sᵀ = S) (hrD : Fintype.card r ≤ D) :
       BHW.sourcePrincipalSchurGraph n e A B S ∈
           BHW.sourceSymmetricRankLEVariety n D ↔
         (Matrix.of fun i j : q => S i j).rank ≤ D - Fintype.card r

   theorem BHW.sourcePrincipalSchurGraph_mem_rankExact_iff
       (n D : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {A : Matrix r r ℂ} (hA_unit : IsUnit A.det)
       (hA_sym : Aᵀ = A)
       {B : Matrix r q ℂ} {S : Matrix q q ℂ}
       (hS_sym : Sᵀ = S) (hrD : Fintype.card r ≤ D) :
       BHW.sourcePrincipalSchurGraph n e A B S ∈
           BHW.sourceSymmetricRankExactStratum n D ↔
         (Matrix.of fun i j : q => S i j).rank = D - Fintype.card r
   ```

   These symmetry and rank-`≤`/rank-exact graph lemmas are also checked in
   `SourceComplexSchurGraph.lean`.  The proof of the rank lemmas is:

   - rewrite the graph's principal block to `A`, so the checked hypothesis
     needed by
     `sourceSymmetricRankLEVariety_iff_principal_schur_rank_le` /
     `sourceSymmetricRankExactStratum_iff_principal_schur_rank_eq` is exactly
     `hA_unit`;
   - rewrite the Schur complement to `S`;
   - discharge the symmetric-matrix conjunct using
     `sourcePrincipalSchurGraph_mem_symmetric`.

   For performance, introduce local abbreviations
   `G := sourcePrincipalSchurGraph n e A B S` and
   `M := Matrix.of fun i j : Fin n => G i j`; rewrite `M.reindex e e` only
   once.  The previous direct prototype timed out because it repeatedly
   unfolded `Matrix.of` and the graph expression inside block simplification.

6. Build the local product neighborhood at a singular point `Z0`.

   Let `D := d + 1`, `k := (Matrix.of fun i j : Fin n => Z0 i j).rank`, and
   assume the singular branch `k < D`.  From
   `sourceComplexGramVariety_eq_rank_le`, `hZ0 : Z0 ∈ sourceComplexGramVariety
   d n` gives symmetry and `k ≤ D`.  Use
   `exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank` with `r = k` to
   choose an injective `I : Fin k -> Fin n` with nonzero principal minor, and
   set

   ```lean
   let q := BHW.selectedIndexComplement I
   let e := BHW.selectedIndexSumEquiv I hI
   let M0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z0 i j
   let A0 : Matrix (Fin k) (Fin k) ℂ := (M0.reindex e e).toBlocks₁₁
   let B0 : Matrix (Fin k) q ℂ := (M0.reindex e e).toBlocks₁₂
   let S0 : Matrix q q ℂ :=
     (M0.reindex e e).toBlocks₂₂ -
       (M0.reindex e e).toBlocks₂₁ * A0⁻¹ * B0
   ```

   Because `Z0` has rank exactly `k` and `A0.det` is a unit, the checked
   `rank_reindexed_principal_eq_card_add_rank_schur` gives
   `S0.rank = 0`, hence `S0 = 0` by `rank_eq_zero`.  Symmetry of `Z0` gives
   `(M0.reindex e e).toBlocks₂₁ = B0ᵀ`, so
   `Z0 = sourcePrincipalSchurGraph n e A0 B0 0`.

   The neighborhood should be chosen in graph coordinates:

   - `Aset`: a small connected open ball around `A0` inside the affine subspace
     of symmetric `Fin k × Fin k` matrices and inside `{A | IsUnit A.det}`;
   - `Bset`: a small connected open ball around `B0` in all rectangular
     `Fin k × q` matrices;
   - `Scone`: the set `C` returned by
     `sourceSymmetricRankExactCone_small_connected (Fintype.card q) (D-k)` for
     a small open neighborhood of `0` in symmetric `q × q` matrices, transported
     along an equivalence `q ≃ Fin (Fintype.card q)` if the existing cone theorem
     is kept on `Fin m`.

   The type-transport step is now checked in
   `BHWPermutation/SourceComplexConeTransport.lean`.  The theorem surface is:

   ```lean
   theorem BHW.matrixSymmetricRankExactCone_small_connected
       {q : Type*} [Fintype q] [DecidableEq q]
       (r : Nat) (hr : r ≤ Fintype.card q)
       {N : Set (Matrix q q ℂ)}
       (hN_open : IsOpen N)
       (h0N : (0 : Matrix q q ℂ) ∈ N) :
       ∃ C : Set (Matrix q q ℂ),
         (0 : Matrix q q ℂ) ∈ C ∧
         IsOpen C ∧ C ⊆ N ∧
         IsConnected
           (C ∩ {S : Matrix q q ℂ | Sᵀ = S ∧ S.rank = r})
   ```

   Proof transcript, now reflected in the checked Lean proof:

   1. Put `m := Fintype.card q` and `e := Fintype.equivFin q`.
   2. Pull `N` back to Fin-coordinates:

      ```lean
      let Nfin : Set (Matrix (Fin m) (Fin m) ℂ) :=
        {T | T.reindex e.symm e.symm ∈ N}
      ```

      `Nfin` is open by `hN_open.preimage` and `fun_prop`; `0 ∈ Nfin` by
      simp.
   3. Apply `sourceSymmetricRankExactCone_small_connected m r hr` to `Nfin`,
      obtaining `Cfin`.
   4. Push the connected neighborhood back:

      ```lean
      let C : Set (Matrix q q ℂ) := {S | S.reindex e e ∈ Cfin}
      ```

      Openness is again a continuous preimage.  The subset `C ⊆ N` follows
      from `Cfin ⊆ Nfin` and the identity
      `(S.reindex e e).reindex e.symm e.symm = S`.
   5. The rank-exact symmetric stratum is transported by reindexing:

      ```lean
      Sᵀ = S ∧ S.rank = r
        ↔ (S.reindex e e)ᵀ = S.reindex e e ∧
          (S.reindex e e).rank = r
      ```

      The rank part is `simp` for reindexing by equivalences; the symmetry
      part is entrywise extensionality.
   6. Hence
      `C ∩ {S | Sᵀ = S ∧ S.rank = r}` is the continuous image under
      `T ↦ T.reindex e.symm e.symm` of
      `Cfin ∩ sourceSymmetricRankExactStratum m r`, so it is connected.

   The exact Lean split should avoid pretending this is ordinary openness in
   the full `(A,B,S)` space.  The honest base is the product of:

   ```lean
   {A | Aᵀ = A} ∩ Metric.ball A0 εA ∩ {A | IsUnit A.det}
   Metric.ball B0 εB
   C ∩ BHW.sourceSymmetricRankExactStratum (Fintype.card q) (D-k)
   ```

   with `S` transported back from `Fin (Fintype.card q)` to `q`.  The
   `A`-factor can be connected by the same small-ball convexity argument used
   for finite-dimensional affine subspaces: line segments preserve symmetry,
   and the ball radius is chosen inside the determinant-unit neighborhood.  The
   `B`-factor is an ordinary connected ball.  The `S`-factor is connected by
   the cone lemma.  Mathlib's product connectedness then gives connectedness
   of the rank-exact parameter set.

   The `A`-factor topology is now checked in `SourceComplexSchurGraph.lean`:

   ```lean
   theorem BHW.isOpen_matrix_det_isUnit
       {r : Type*} [Fintype r] [DecidableEq r] :
       IsOpen ({A : Matrix r r ℂ | IsUnit A.det})

   theorem BHW.exists_pos_ball_subset_isUnit_det
       {r : Type*} [Fintype r] [DecidableEq r]
       {A0 : Matrix r r ℂ} (hA0 : IsUnit A0.det) :
       ∃ ε : ℝ, 0 < ε ∧
         Metric.ball A0 ε ⊆ {A : Matrix r r ℂ | IsUnit A.det}

   theorem BHW.isConnected_symmetric_matrix_ball
       {r : Type*} [Fintype r] [DecidableEq r]
       {A0 : Matrix r r ℂ} (hA0sym : A0ᵀ = A0)
       {ε : ℝ} (hε : 0 < ε) :
       IsConnected (Metric.ball A0 ε ∩ {A : Matrix r r ℂ | Aᵀ = A})

   theorem BHW.isConnected_matrix_ball
       {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (B0 : Matrix r q ℂ) {ε : ℝ} (hε : 0 < ε) :
       IsConnected (Metric.ball B0 ε)
   ```

   The implementation uses the Frobenius matrix norm scope for matrix metric
   balls.  This choice is harmless: all finite-dimensional norms give the same
   local topology, and this lemma only needs a concrete connected ball.

   The Schur-coordinate continuity needed for relative openness is now checked
   as well:

   ```lean
   theorem BHW.continuousOn_principalBlock_invEntry
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q) (i j : r) :
       ContinuousOn
         (fun Z : Matrix (Fin n) (Fin n) ℂ =>
           ((Z.reindex e e).toBlocks₁₁)⁻¹ i j)
         {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)}

   theorem BHW.continuousOn_reindexedPrincipalSchurComplement
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q) :
       ContinuousOn
         (fun Z : Matrix (Fin n) (Fin n) ℂ =>
           BHW.reindexedRectSchurComplement Z e e)
         {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)}
   ```

   The second proof is again coordinatewise: expand the Schur complement entry
   as

   ```lean
   C α β -
     ∑ x, (∑ y, B₂₁ α y * A⁻¹ y x) * B₁₂ x β
   ```

   and combine finite sums/products of continuous scalar coordinate functions.

   The ambient openness package for the final `V` is now checked:

   ```lean
   theorem BHW.isOpen_sourcePrincipalSchurCoordinatePatch
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {N0 : Set (Matrix (Fin n) (Fin n) ℂ)}
       (hN0_open : IsOpen N0)
       {Aset : Set (Matrix r r ℂ)}
       (hAset_open : IsOpen Aset)
       {Bset : Set (Matrix r q ℂ)}
       (hBset_open : IsOpen Bset)
       {Sset : Set (Matrix q q ℂ)}
       (hSset_open : IsOpen Sset) :
       IsOpen
         {Z : Matrix (Fin n) (Fin n) ℂ |
           Z ∈ N0 ∧
           IsUnit ((Z.reindex e e).toBlocks₁₁.det) ∧
           (Z.reindex e e).toBlocks₁₁ ∈ Aset ∧
           (Z.reindex e e).toBlocks₁₂ ∈ Bset ∧
           BHW.reindexedRectSchurComplement Z e e ∈ Sset}
   ```

   Thus the final relatively open chart is obtained by taking this open ambient
   set and intersecting it with `sourceComplexGramVariety d n`, exactly as
   required by `IsRelOpenInSourceComplexGramVariety`.

   The topology lemmas needed before the final local-basis theorem are now
   precisely these, in this order:

   ```lean
   theorem BHW.continuousOn_matrix_inv_of_isUnit_det
       {q : Type*} [Fintype q] [DecidableEq q] :
       ContinuousOn (fun A : Matrix q q ℂ => A⁻¹)
         {A : Matrix q q ℂ | IsUnit A.det}

   theorem BHW.continuousOn_sourcePrincipalSchurGraph
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q) :
       ContinuousOn
         (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
           BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2)
         {p | IsUnit p.1.det}

   theorem BHW.exists_sourcePrincipalSchurGraph_product_subset_open
       (n : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {A0 : Matrix r r ℂ} {B0 : Matrix r q ℂ} {S0 : Matrix q q ℂ}
       (hA0_unit : IsUnit A0.det)
       {N0 : Set (Fin n -> Fin n -> ℂ)}
       (hN0_open : IsOpen N0)
       (hG0N0 : BHW.sourcePrincipalSchurGraph n e A0 B0 S0 ∈ N0) :
       ∃ Aset : Set (Matrix r r ℂ),
       ∃ Bset : Set (Matrix r q ℂ),
       ∃ Sset : Set (Matrix q q ℂ),
         IsOpen Aset ∧ A0 ∈ Aset ∧
         IsOpen Bset ∧ B0 ∈ Bset ∧
         IsOpen Sset ∧ S0 ∈ Sset ∧
         (∀ A ∈ Aset, IsUnit A.det) ∧
         ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
             BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧ p.2.2 ∈ Sset}) ⊆ N0

   theorem BHW.isConnected_sourcePrincipalSchurGraph_rankExact_image
       (n D : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {Aset : Set (Matrix r r ℂ)}
       {Bset : Set (Matrix r q ℂ)}
       {Sset : Set (Matrix q q ℂ)}
       (hA_conn : IsConnected Aset)
       (hB_conn : IsConnected Bset)
       (hS_conn :
         IsConnected
           (Sset ∩ {S : Matrix q q ℂ |
             Sᵀ = S ∧ S.rank = D - Fintype.card r}))
       (hA_unit : ∀ A ∈ Aset, IsUnit A.det) :
       IsConnected
         ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
             BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           ({p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
             p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
               Sᵀ = S ∧ S.rank = D - Fintype.card r}}))

   theorem BHW.sourcePrincipalSchurGraph_rankExact_image_subset
       (n D : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {Aset : Set (Matrix r r ℂ)}
       {Bset : Set (Matrix r q ℂ)}
       {Sset : Set (Matrix q q ℂ)}
       (hA_unit : ∀ A ∈ Aset, IsUnit A.det)
       (hA_sym : ∀ A ∈ Aset, Aᵀ = A)
       (hrD : Fintype.card r ≤ D) :
       ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
           BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
         {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
           p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
             Sᵀ = S ∧ S.rank = D - Fintype.card r}}) ⊆
         BHW.sourceSymmetricRankExactStratum n D
   ```

   The inverse-continuity theorem is now checked in
   `SourceComplexSchurGraph.lean`.  Its proof uses Mathlib's
   `Matrix.inv_def : A⁻¹ = Ring.inverse A.det • A.adjugate`.  On
   `{A | IsUnit A.det}`, the determinant is nonzero, scalar inverse is
   continuous, and the adjugate entries are polynomial in the entries of `A`.
   This is a finite-dimensional algebra lemma, not an OS-specific axiom.

   The product-neighborhood theorem is also checked in
   `SourceComplexSchurGraph.lean`.  Its proof forms the open set
   `{p | IsUnit p.1.det} ∩ graph ⁻¹' N0`, applies
   `continuousOn_sourcePrincipalSchurGraph`, and then uses the product-neighborhood
   basis twice to split a neighborhood of `(A0,B0,S0)` into open `A`, `B`, and
   `S` neighborhoods.  The returned `A` neighborhood is already contained in
   the determinant-unit locus.

   These two graph-image theorems are now checked in
   `SourceComplexSchurGraph.lean`.  The connected-image theorem is product
   connectedness followed by `continuousOn_sourcePrincipalSchurGraph`.  The
   rank-exact image-subset theorem applies the checked
   `sourcePrincipalSchurGraph_mem_rankExact_iff`.

   The exact patch/image equality needed by the singular local-basis theorem is
   now checked too:

   ```lean
   theorem BHW.sourcePrincipalSchurGraph_rankExact_image_eq_coordinatePatch
       (n D : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {N0 : Set (Fin n -> Fin n -> ℂ)}
       {Aset : Set (Matrix r r ℂ)}
       {Bset : Set (Matrix r q ℂ)}
       {Sset : Set (Matrix q q ℂ)}
       (hA_unit : ∀ A ∈ Aset, IsUnit A.det)
       (hA_sym : ∀ A ∈ Aset, Aᵀ = A)
       (hrD : Fintype.card r ≤ D)
       (hgraph_N0 :
         ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
             BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
             p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
               Sᵀ = S ∧ S.rank = D - Fintype.card r}}) ⊆ N0) :
       ({Z : Fin n -> Fin n -> ℂ |
           Z ∈ N0 ∧
           IsUnit
             ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
           (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
             Aset ∧
           (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
             Bset ∧
           BHW.reindexedRectSchurComplement
             (Matrix.of fun i j : Fin n => Z i j) e e ∈ Sset} ∩
         BHW.sourceSymmetricRankExactStratum n D) =
         ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
             BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
             p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
               Sᵀ = S ∧ S.rank = D - Fintype.card r}})

   theorem BHW.sourcePrincipalSchurGraph_rankExact_image_eq_openCoordinatePatch
       (n D : Nat) {r q : Type*} [Fintype r] [Fintype q]
       [DecidableEq r] [DecidableEq q]
       (e : Fin n ≃ r ⊕ q)
       {N0 : Set (Fin n -> Fin n -> ℂ)}
       {Aset : Set (Matrix r r ℂ)}
       {Bset : Set (Matrix r q ℂ)}
       {Sset : Set (Matrix q q ℂ)}
       (hA_unit : ∀ A ∈ Aset, IsUnit A.det)
       (hrD : Fintype.card r ≤ D)
       (hgraph_N0 :
         ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
             BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           {p | p.1 ∈ Aset ∩ {A : Matrix r r ℂ | Aᵀ = A} ∧
             p.2.1 ∈ Bset ∧
             p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
               Sᵀ = S ∧ S.rank = D - Fintype.card r}}) ⊆ N0) :
       ({Z : Fin n -> Fin n -> ℂ |
           Z ∈ N0 ∧
           IsUnit
             ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
           (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
             Aset ∧
           (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
             Bset ∧
           BHW.reindexedRectSchurComplement
             (Matrix.of fun i j : Fin n => Z i j) e e ∈ Sset} ∩
         BHW.sourceSymmetricRankExactStratum n D) =
         ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
             BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           {p | p.1 ∈ Aset ∩ {A : Matrix r r ℂ | Aᵀ = A} ∧
             p.2.1 ∈ Bset ∧
             p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
               Sᵀ = S ∧ S.rank = D - Fintype.card r}})
   ```

   Forward direction: a rank-exact `Z` in the coordinate patch has symmetric
   `A` and `S` coordinates, Schur rank `D-k` by the principal Schur rank
   theorem, and equals its graph by
   `sourcePrincipalSchurGraph_coordinates_eq_of_symmetric`.  Reverse direction:
   block recovery gives the patch coordinates, `hgraph_N0` gives the ambient
   neighborhood condition, and
   `sourcePrincipalSchurGraph_mem_rankExact_iff` gives rank-exact membership.
   The open-coordinate variant packages the additional fact that on a
   rank-exact symmetric matrix the open `Aset` condition may be replaced by
   `Aset ∩ {A | Aᵀ = A}` for the graph parameters; it is the preferred equality
   for the final local-basis proof.

   This theorem is now checked in `SourceComplexSchurGraph.lean`.  The Lean
   proof is coordinatewise, because a direct `fun_prop` on the unfolded graph
   expands too much matrix notation.  After

   ```lean
   rw [continuousOn_pi]
   intro i
   rw [continuousOn_pi]
   intro j
   unfold sourcePrincipalSchurGraph
   cases e i <;> cases e j
   ```

   the four coordinate cases are:

   - upper-left: `p ↦ p.1 a b`;
   - upper-right: `p ↦ p.2.1 a β`;
   - lower-left: `p ↦ p.2.1 b α`;
   - lower-right:

     ```lean
     p ↦ p.2.2 α β +
       ∑ x, ∑ y,
         p.2.1 y α * p.1⁻¹ y x * p.2.1 x β
     ```

   The first three are `fun_prop`.  For the lower-right case, first prove
   `ContinuousOn (fun p => p.1⁻¹ y x) {p | IsUnit p.1.det}` from
   `continuousOn_matrix_inv_of_isUnit_det` and coordinate evaluation.  Then use
   finite sums/products of continuous-on scalar coordinate functions.  This
   avoids asking automation to discover continuity of matrix transpose and
   multiplication at the whole matrix-valued level.

7. Push the product through the graph map.

   Choose radii so that the continuous graph map sends the parameter product
   into `N0`.  Define

   ```lean
   let V : Set (Fin n -> Fin n -> ℂ) :=
     {Z |
       Z ∈ N0 ∧
       Z ∈ BHW.sourceComplexGramVariety d n ∧
       let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z i j
       IsUnit ((M.reindex e e).toBlocks₁₁.det) ∧
       (M.reindex e e).toBlocks₁₁ ∈ Aball ∧
       (M.reindex e e).toBlocks₁₂ ∈ Bball ∧
       BHW.reindexedRectSchurComplement M e e ∈ Sambient}
   ```

   Here `Aball := Metric.ball A0 εA`, `Bball := Metric.ball B0 εB`,
   `Sambient := C`, and the rank-exact parameter set used for connectedness is

   ```lean
   let Aexact : Set (Matrix (Fin k) (Fin k) ℂ) :=
     Aball ∩ {A | Aᵀ = A}
   let Sexact : Set (Matrix q q ℂ) :=
     Sambient ∩ {S | Sᵀ = S ∧ S.rank = D - k}
   ```

   The determinant-unit condition on `Aexact` is supplied by choosing `εA`
   with `Metric.ball A0 εA ⊆ {A | IsUnit A.det}`.

   This `V` is relatively open in the source complex Gram variety because:

   - `N0` is ambient open;
   - the determinant-unit condition is open;
   - block projection and Schur-complement maps are continuous on the
     determinant-unit patch;
   - `Aball`, `Bball`, and `Sambient` are open in their intended ambient spaces.

   On this patch, the inverse coordinate map is explicit:

   ```lean
   Z ↦
     ( (M.reindex e e).toBlocks₁₁,
       (M.reindex e e).toBlocks₁₂,
       (M.reindex e e).toBlocks₂₂ -
         (M.reindex e e).toBlocks₂₁ *
           (M.reindex e e).toBlocks₁₁⁻¹ *
           (M.reindex e e).toBlocks₁₂ )
   ```

   and the checked Schur rank theorem proves:

   - if `Z ∈ V ∩ sourceSymmetricRankExactStratum n D`, then the Schur
     complement coordinate has rank `D-k` by
     `sourceSymmetricRankExactStratum_iff_principal_schur_rank_eq`; symmetry of
     `Z` gives symmetry of the `A` and `S` coordinates by
     `principalBlock_transpose_eq_of_symmetric` and
     `reindexedRectSchurComplement_transpose_eq_of_symmetric`, so the coordinate
     triple lies in `Aexact × Bball × Sexact`;
   - every such `Z` is the graph of its coordinates by the checked theorem
     `sourcePrincipalSchurGraph_coordinates_eq_of_symmetric`;
   - conversely, every graph point from `Aexact × Bball × Sexact` lies in
     `V ∩ sourceSymmetricRankExactStratum n D` by
     `sourcePrincipalSchurGraph_rankExact_image_subset`.

   Therefore `V ∩ rankExact` is exactly the continuous graph image of the
   connected product.  This proves the singular branch of
   `sourceComplexGramVariety_local_rankExact_connected_basis`.

   Lean-ready singular branch assembly:

   ```lean
   -- inside sourceComplexGramVariety_local_rankExact_connected_basis
   let D : Nat := d + 1
   let M0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z0 i j
   let k : Nat := M0.rank
   have hZ0sym : Z0 ∈ BHW.sourceSymmetricMatrixSpace n := by
     rw [BHW.sourceComplexGramVariety_eq_rank_le] at hZ0
     exact hZ0.1
   have hkD : k ≤ D := by
     rw [BHW.sourceComplexGramVariety_eq_rank_le] at hZ0
     simpa [D, k, M0] using hZ0.2
   by_cases hkreg : k = D
   · have hZ0reg : Z0 ∈ BHW.sourceSymmetricRankExactStratum n D := by
       exact ⟨hZ0sym, by simpa [D, k, M0] using hkreg⟩
     obtain ⟨z0, hz0_regular, hz0_gram⟩ :=
       BHW.sourceSymmetricRankExactStratum_exists_complexRegular_realization
         d n (Nat.le_of_lt hD) (by simpa [D] using hZ0reg)
     let Vsrc : Set (Fin n -> Fin (d + 1) -> ℂ) :=
       {z | BHW.sourceMinkowskiGram d n z ∈ N0}
     have hVsrc_open : IsOpen Vsrc :=
       hN0_open.preimage (BHW.contDiff_sourceMinkowskiGram d n).continuous
     have hz0Vsrc : z0 ∈ Vsrc := by
       simpa [Vsrc, hz0_gram] using hZ0N0
     obtain ⟨Usrc, hUsrc_open, hUsrc_conn, hz0_Usrc, hUsrc_sub,
         O, hZ0O, hO_rel, hO_image, hO_rank, hO_conn, hO_surj⟩ :=
       BHW.sourceComplexGramMap_localConnectedRelOpenImage_in_open_of_complexRegular
         d n (Nat.le_of_lt hD) hz0_regular hVsrc_open hz0Vsrc
     refine ⟨O, hZ0O, hO_rel, ?_, ?_⟩
     · intro G hGO
       rcases hO_surj G hGO with ⟨z, hzU, hzG⟩
       refine ⟨?_, ?_⟩
       · rw [← hzG]
         exact hUsrc_sub hzU
       · exact BHW.sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
           d n (d + 1) (Nat.le_refl (d + 1)) (hO_rank hGO)
     · have hO_inter :
           O ∩ BHW.sourceSymmetricRankExactStratum n (d + 1) = O := by
         ext G
         constructor
         · intro hG
           exact hG.1
         · intro hG
           exact ⟨hG, hO_rank hG⟩
       rw [hO_inter]
       exact hO_conn
   · have hksing : k < D := lt_of_le_of_ne hkD hkreg
     obtain ⟨I, hI, hminor⟩ :=
       BHW.exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank
         (n := n) (r := k) hZ0sym rfl
     let q := BHW.selectedIndexComplement I
     let e : Fin n ≃ Fin k ⊕ q := BHW.selectedIndexSumEquiv I hI
     let A0 : Matrix (Fin k) (Fin k) ℂ := (M0.reindex e e).toBlocks₁₁
     let B0 : Matrix (Fin k) q ℂ := (M0.reindex e e).toBlocks₁₂
     let S0 : Matrix q q ℂ := BHW.reindexedRectSchurComplement M0 e e
   ```

   The selected minor gives the determinant-unit principal block:

   ```lean
   have hA0_unit : IsUnit A0.det := by
     simpa [A0, M0, e] using
       BHW.isUnit_selectedIndexSumEquiv_toBlocks₁₁_det
         (I := I) (J := I) hI hI hminor
   ```

   The Schur complement of the basepoint is zero:

   ```lean
   have hS0_rank_zero : S0.rank = 0 := by
     have hsplit :=
       BHW.rank_reindexed_principal_eq_card_add_rank_schur
         (Z := M0) (e := e) hA0_unit
     -- `hsplit : M0.rank = k + S0.rank`.
     -- Since `k = M0.rank`, `omega` gives `S0.rank = 0`.
     omega

   have hS0_zero : S0 = 0 :=
     BHW.matrix_eq_zero_of_rank_eq_zero S0 hS0_rank_zero

   have hZ0_graph :
       BHW.sourcePrincipalSchurGraph n e A0 B0 0 = Z0 := by
     have hM0sym : M0ᵀ = M0 := by
       ext i j
       simpa [M0, Matrix.transpose] using hZ0sym j i
     have hcoord :=
       BHW.sourcePrincipalSchurGraph_coordinates_eq_of_symmetric n e hM0sym
     -- rewrite `S0` to `0` and read the matrix equality coordinatewise.
     funext i j
     have hij := congr_fun (congr_fun hcoord i) j
     simpa [M0, A0, B0, S0, hS0_zero] using hij
   ```

   Extract product neighborhoods from graph continuity:

   ```lean
   obtain ⟨UA, UB, US,
       hUA_open, hA0_UA, hUB_open, hB0_UB, hUS_open, h0_US,
       hUA_unit, hgraph_U⟩ :=
     BHW.exists_sourcePrincipalSchurGraph_product_subset_open
       (n := n) (e := e) (A0 := A0) (B0 := B0) (S0 := 0)
       hA0_unit hN0_open
       (by simpa [hZ0_graph] using hZ0N0)
   ```

   Shrink these neighborhoods to the connected factors used for the rank-exact
   product:

   ```lean
   -- choose εA with `Metric.ball A0 εA ⊆ UA`
   -- choose εB with `Metric.ball B0 εB ⊆ UB`
   -- apply the transported cone theorem to `US` at the zero Schur coordinate
   have hq_card : Fintype.card q = n - k := by
     -- from `Fintype.card_congr e : n = k + Fintype.card q`
     omega
   have hDk_le_q : D - k ≤ Fintype.card q := by omega
   obtain ⟨C, h0C, hC_open, hC_sub_US, hC_rank_conn⟩ :=
     BHW.matrixSymmetricRankExactCone_small_connected
       (q := q) (r := D - k) hDk_le_q hUS_open h0_US

   let Aball : Set (Matrix (Fin k) (Fin k) ℂ) := Metric.ball A0 εA
   let Bball : Set (Matrix (Fin k) q ℂ) := Metric.ball B0 εB
   let Aexact : Set (Matrix (Fin k) (Fin k) ℂ) :=
     Aball ∩ {A | Aᵀ = A}
   ```

   The connectedness inputs are now all checked consumers:

   ```lean
   have hAexact_conn : IsConnected Aexact :=
     BHW.isConnected_symmetric_matrix_ball hA0_sym hεA
   have hBball_conn : IsConnected Bball :=
     BHW.isConnected_matrix_ball B0 hεB
   have hSexact_conn :
       IsConnected (C ∩ {S : Matrix q q ℂ |
         Sᵀ = S ∧ S.rank = D - k}) :=
     hC_rank_conn
   have hgraph_rank_conn :
       IsConnected
         ((fun p => BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           {p | p.1 ∈ Aexact ∧ p.2.1 ∈ Bball ∧
             p.2.2 ∈ C ∩ {S : Matrix q q ℂ |
               Sᵀ = S ∧ S.rank = D - k}}) :=
     BHW.isConnected_sourcePrincipalSchurGraph_rankExact_image
       n D e hAexact_conn hBball_conn hSexact_conn
       (by
         intro A hA
         exact hUA_unit A (hAball_sub_UA hA.1))
   ```

   Define the actual relatively open source-variety neighborhood using the
   open factors, not the closed symmetric factors:

   ```lean
   let V0 : Set (Fin n -> Fin n -> ℂ) :=
     {Z |
       Z ∈ N0 ∧
       IsUnit
         ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
       (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
         Aball ∧
       (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
         Bball ∧
       BHW.reindexedRectSchurComplement
         (Matrix.of fun i j : Fin n => Z i j) e e ∈ C}
   let V : Set (Fin n -> Fin n -> ℂ) :=
     V0 ∩ BHW.sourceComplexGramVariety d n
   ```

   Relative openness follows directly from
   `isOpen_sourcePrincipalSchurCoordinatePatch`:

   ```lean
   have hV_rel : BHW.IsRelOpenInSourceComplexGramVariety d n V := by
     refine ⟨V0, ?_, rfl⟩
     exact
       BHW.isOpen_sourcePrincipalSchurCoordinatePatch
         (n := n) (e := e)
         hN0_open isOpen_ball isOpen_ball hC_open
   ```

   Membership and containment:

   ```lean
   have hZ0V : Z0 ∈ V := by
     refine ⟨?_, hZ0⟩
     have hZ0_matrix_graph :
         (Matrix.of fun i j : Fin n => Z0 i j) =
           Matrix.of fun i j : Fin n =>
             BHW.sourcePrincipalSchurGraph n e A0 B0 0 i j := by
       ext i j
       simpa [hZ0_graph]
     refine ⟨hZ0N0, ?_, ?_, ?_, ?_⟩
     · rw [hZ0_matrix_graph,
         BHW.sourcePrincipalSchurGraph_toBlocks₁₁ n e A0 B0 0]
       exact hA0_unit
     · rw [hZ0_matrix_graph,
         BHW.sourcePrincipalSchurGraph_toBlocks₁₁ n e A0 B0 0]
       exact Metric.mem_ball_self hεA
     · rw [hZ0_matrix_graph,
         BHW.sourcePrincipalSchurGraph_toBlocks₁₂ n e A0 B0 0]
       exact Metric.mem_ball_self hεB
     · change
         BHW.reindexedRectSchurComplement
           (Matrix.of fun i j : Fin n => Z0 i j) e e ∈ C
       rw [hZ0_matrix_graph]
       change
         ((Matrix.of fun i j : Fin n =>
             BHW.sourcePrincipalSchurGraph n e A0 B0 0 i j).reindex e e).toBlocks₂₂ -
           ((Matrix.of fun i j : Fin n =>
             BHW.sourcePrincipalSchurGraph n e A0 B0 0 i j).reindex e e).toBlocks₂₁ *
             ((Matrix.of fun i j : Fin n =>
               BHW.sourcePrincipalSchurGraph n e A0 B0 0 i j).reindex e e).toBlocks₁₁⁻¹ *
             ((Matrix.of fun i j : Fin n =>
               BHW.sourcePrincipalSchurGraph n e A0 B0 0 i j).reindex e e).toBlocks₁₂ ∈ C
       rw [BHW.sourcePrincipalSchurGraph_schurComplement n e A0 B0 0]
       exact h0C

   have hV_sub : V ⊆ N0 ∩ BHW.sourceComplexGramVariety d n := by
     intro Z hZ
     exact ⟨hZ.1.1, hZ.2⟩
   ```

   Finally identify the punctured chart with the connected graph image.  Because
   `V0` uses `Aball` while the graph theorem uses
   `Aexact = Aball ∩ {A | Aᵀ = A}`, first rewrite the rank-exact intersection:
   if `Z ∈ sourceSymmetricRankExactStratum n D`, then
   `principalBlock_transpose_eq_of_symmetric` puts its `A` coordinate in the
   symmetric factor, so the `Aball` patch and `Aexact` patch agree after
   intersecting with the rank-exact stratum.  Then apply the checked equality:

   ```lean
   have hpatch_eq :
       V ∩ BHW.sourceSymmetricRankExactStratum n D =
         ((fun p => BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           {p | p.1 ∈ Aexact ∧ p.2.1 ∈ Bball ∧
             p.2.2 ∈ C ∩ {S : Matrix q q ℂ |
               Sᵀ = S ∧ S.rank = D - k}}) := by
     have hrank_sub_var :
         BHW.sourceSymmetricRankExactStratum n D ⊆
           BHW.sourceComplexGramVariety d n := by
       simpa [D] using
         BHW.sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
           d n (d + 1) (Nat.le_refl (d + 1))

     have hV_to_Aexact :
         V ∩ BHW.sourceSymmetricRankExactStratum n D =
           ({Z : Fin n -> Fin n -> ℂ |
             Z ∈ N0 ∧
             IsUnit
               ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
             (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
               Aexact ∧
             (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
               Bball ∧
             BHW.reindexedRectSchurComplement
               (Matrix.of fun i j : Fin n => Z i j) e e ∈ C} ∩
             BHW.sourceSymmetricRankExactStratum n D) := by
       ext Z
       constructor
       · rintro ⟨⟨hV0, _hZvar⟩, hZrank⟩
         rcases hV0 with ⟨hZN0, hUnit, hA_ball, hB_ball, hS_C⟩
         let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z i j
         have hM_sym : Mᵀ = M := by
           ext i j
           simpa [M, Matrix.transpose] using hZrank.1 j i
         have hA_sym :
             ((M.reindex e e).toBlocks₁₁)ᵀ =
               (M.reindex e e).toBlocks₁₁ :=
           BHW.principalBlock_transpose_eq_of_symmetric n e hM_sym
         exact
           ⟨⟨hZN0, hUnit, ⟨by simpa [M] using hA_ball, hA_sym⟩,
              hB_ball, hS_C⟩, hZrank⟩
       · rintro ⟨hpatch, hZrank⟩
         rcases hpatch with ⟨hZN0, hUnit, hA_exact, hB_ball, hS_C⟩
         exact
           ⟨⟨⟨hZN0, hUnit, hA_exact.1, hB_ball, hS_C⟩,
              hrank_sub_var hZrank⟩, hZrank⟩

     have hgraph_N0 :
         ((fun p => BHW.sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
           {p | p.1 ∈ Aexact ∧ p.2.1 ∈ Bball ∧
             p.2.2 ∈ C ∩ {S : Matrix q q ℂ |
               Sᵀ = S ∧ S.rank = D - k}}) ⊆ N0 := by
       rintro G ⟨p, hp, rfl⟩
       apply hgraph_U
       refine ⟨p, ?_, rfl⟩
       exact
         ⟨hAball_sub_UA hp.1.1,
          hBball_sub_UB hp.2.1,
          hC_sub_US hp.2.2.1⟩

     have hpatch_graph :=
       BHW.sourcePrincipalSchurGraph_rankExact_image_eq_coordinatePatch
         (n := n) (D := D) (e := e) (N0 := N0)
         (Aset := Aexact) (Bset := Bball) (Sset := C)
         (by
           intro A hA
           exact hUA_unit A (hAball_sub_UA hA.1))
         (by
           intro A hA
           exact hA.2)
         (by simpa [D] using hkD)
         hgraph_N0
     rw [hV_to_Aexact, hpatch_graph]

   have hV_rank_conn :
       IsConnected (V ∩ BHW.sourceSymmetricRankExactStratum n D) := by
     rw [hpatch_eq]
     exact hgraph_rank_conn
   ```

   This completes the singular branch and supplies the required witness
   `⟨V, hZ0V, hV_rel, hV_sub, hV_rank_conn⟩`.

The principal-minor step in item 3 is now checked in
`BHWPermutation/SourceComplexSchurPatch.lean`:

```lean
theorem BHW.exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank
    {n r : Nat} {Z : Fin n -> Fin n -> ℂ}
    (hZsym : Z ∈ BHW.sourceSymmetricMatrixSpace n)
    (hrank : (Matrix.of fun i j : Fin n => Z i j).rank = r) :
    ∃ I : Fin r -> Fin n, Function.Injective I ∧
      BHW.sourceMatrixMinor n r I I Z ≠ 0
```

The proof uses the already checked complex symmetric rank factorization:
factor `Z = A Aᵀ` with `A : Fin n -> Fin r -> ℂ`; exact rank `r` forces
`A` to have full column rank, so a nonzero row minor of `A` gives a nonzero
principal minor of `A Aᵀ`.

The singular Schur-chart branch is now checked as:

```lean
theorem BHW.sourceComplexGramVariety_local_rankExact_connected_basis_singular
    (d n : Nat)
    (hD : d + 1 < n)
    {Z0 : Fin n -> Fin n -> ℂ}
    (hZ0 : Z0 ∈ BHW.sourceComplexGramVariety d n)
    (hZ0_sing :
      (Matrix.of fun i j : Fin n => Z0 i j).rank < d + 1)
    {N0 : Set (Fin n -> Fin n -> ℂ)}
    (hN0_open : IsOpen N0)
    (hZ0N0 : Z0 ∈ N0) :
    ∃ V : Set (Fin n -> Fin n -> ℂ),
      Z0 ∈ V ∧
      BHW.IsRelOpenInSourceComplexGramVariety d n V ∧
      V ⊆ N0 ∩ BHW.sourceComplexGramVariety d n ∧
      IsConnected
        (V ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
```

The full local-basis theorem is now checked by splitting on
`(Matrix.of fun i j : Fin n => Z0 i j).rank = d + 1`: the regular branch calls
`sourceComplexGramVariety_local_rankExact_connected_basis_regular`, and the
strictly lower-rank branch calls
`sourceComplexGramVariety_local_rankExact_connected_basis_singular`.

**0z-3. Global connected regular-locus theorem.**

This production theorem is now checked as a short assembly:

```lean
theorem BHW.sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
    (d n : Nat)
    (hD : d + 1 < n)
    {U : Set (Fin n -> Fin n -> ℂ)}
    (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
    (hU_conn : IsConnected U) :
    IsConnected
      (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)) := by
  exact
    BHW.sourceComplexGramVariety_rankExact_inter_relOpen_isConnected_of_local_basis
      d n hU_conn
      (BHW.sourceComplexGramVariety_relOpen_subset_closure_inter_rankExact
        d n (Nat.le_of_lt hD) hU_rel)
      (by
        intro Z hZU N0 hN0_open hZN0
        rcases hU_rel with ⟨U0, hU0_open, hU_eq⟩
        have hZU0 : Z ∈ U0 := by
          rw [hU_eq] at hZU
          exact hZU.1
        have hZvar : Z ∈ BHW.sourceComplexGramVariety d n := by
          rw [hU_eq] at hZU
          exact hZU.2
        rcases BHW.sourceComplexGramVariety_local_rankExact_connected_basis
            d n hD hZvar (hU0_open.inter hN0_open) ⟨hZU0, hZN0⟩ with
          ⟨V, hZV, hV_rel, hV_sub, hV_conn⟩
        refine ⟨V, hZV, hV_rel, ?_, hV_conn⟩
        intro G hGV
        rcases hV_sub hGV with ⟨hGU0N0, hGvar⟩
        exact ⟨by
          rw [hU_eq]
          exact ⟨hGU0N0.1, hGvar⟩, hGU0N0.2⟩
```

The key Lean bookkeeping is that the local-basis theorem is applied inside the
ambient open set `U0 ∩ N0`, where `U = U0 ∩ sourceComplexGramVariety d n` is
the relative-openness witness for `U`.  Therefore the resulting `V` is already
contained in both `U` and `N0`; no extra intersection with `U` is needed after
the local theorem returns.

**0z-4. Rank-exact identity principle assembly.**

This step is checked in Lean in conditional form.  The theorem
`sourceComplexGramVariety_rankExact_identity_principle_of_connected` proves
the global propagation on the rank-exact locus from the supplied geometric
hypothesis that `U ∩ rankExact` is connected.

```lean
theorem BHW.sourceComplexGramVariety_rankExact_identity_principle_of_connected
    (d n : Nat)
    (hD : d + 1 < n)
    {U W : Set (Fin n -> Fin n -> ℂ)}
    {H : (Fin n -> Fin n -> ℂ) -> ℂ}
    (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
    (hUreg_conn :
      IsConnected
        (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
    (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : BHW.SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0
      (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1))
```

Checked proof transcript:

1. Let `Ureg := U ∩ sourceSymmetricRankExactStratum n (d + 1)`.
2. Let `A0` be the ambient union of open sets `O` such that
   `Set.EqOn H 0 (O ∩ Ureg)`, and let `A := A0 ∩ Ureg`.  This avoids a
   circular attempt to prove the whole zero set open before using local
   propagation.
3. `A0` is open by construction, hence `A` is relatively open in `Ureg`.
4. Nonemptiness: apply
   `sourceComplexGramVariety_relOpen_inter_rankExact_nonempty` to `W`, then
   use `hW_sub` and `hW_zero`.
5. Relative closedness of `A` in `Ureg`: if `Z0 ∈ closure A ∩ Ureg`, apply the
   same checked local identity theorem with the real closure hypothesis; it
   gives a relatively open rank-exact neighborhood of `Z0` contained in the
   zero set, hence `Z0 ∈ A`.
6. Use `hUreg_conn`: a nonempty clopen subset of the connected subtype `Ureg`
   is all of `Ureg`.

The strict theorem is now checked as a one-line assembly using 0z-3:

```lean
theorem BHW.sourceComplexGramVariety_rankExact_identity_principle
    (d n : Nat)
    (hD : d + 1 < n)
    {U W : Set (Fin n -> Fin n -> ℂ)}
    {H : (Fin n -> Fin n -> ℂ) -> ℂ}
    (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
    (hU_conn : IsConnected U)
    (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : BHW.SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0
      (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)) := by
  exact
    BHW.sourceComplexGramVariety_rankExact_identity_principle_of_connected
      d n hD hU_rel
      (BHW.sourceComplexGramVariety_rankExact_inter_relOpen_isConnected
        d n hD hU_rel hU_conn)
      hW_rel hW_ne hW_sub hH hW_zero
```

The dense-rank-exact extension to all of `U` is also checked conditionally:

```lean
theorem BHW.sourceComplexGramVariety_identity_principle_of_connected_rankExact
    (d n : Nat)
    (hD : d + 1 < n)
    {U W : Set (Fin n -> Fin n -> ℂ)}
    {H : (Fin n -> Fin n -> ℂ) -> ℂ}
    (hU_rel : BHW.IsRelOpenInSourceComplexGramVariety d n U)
    (hUreg_conn :
      IsConnected
        (U ∩ BHW.sourceSymmetricRankExactStratum n (d + 1)))
    (hW_rel : BHW.IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : BHW.SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 U
```

It applies
`sourceComplexGramVariety_rankExact_identity_principle_of_connected` on
`U ∩ rankExact`, then
`sourceComplexGramVariety_relOpen_eqOn_zero_of_eqOn_rankExact` using
`SourceVarietyHolomorphicOn.continuousOn`.  Since 0z-3 is now checked, the
strict full-domain theorem is the conditional theorem with
`sourceComplexGramVariety_rankExact_inter_relOpen_isConnected`, and the final
arity split `sourceComplexGramVariety_identity_principle` is checked in
`SourceComplexDensity.lean`.

Deep Research route-risk audit
`v1_ChdsVFR2YVpiQUN0U1lfdU1Qa1pidjZBMBIXbFRUdmFaYkFDdFNZX3VNUGtaYnY2QTA`
agrees with this theorem shape: the decomposition is faithful to
Hall-Wightman and the OS-II `E -> R` route, the full-matrix totally-real
shortcut is invalid in the rank-bounded scalar-product variety, and the global
step is an identity theorem for irreducible complex analytic varieties.  The
audit also flags the Lean risks that must stay explicit:

1. `SourceVarietyHolomorphicOn` must remain the strong/local-ambient
   holomorphic representative notion.  This is already the production
   definition: every point of `U` has an ambient open neighborhood on which the
   representative is complex differentiable, with the local variety slice
   contained in `U`.
2. The global identity principle must handle singular lower-rank points through
   analytic-variety irreducibility plus continuity/local ambient holomorphy; do
   not replace it by propagation on the regular stratum unless the density,
   local connectedness, and closure steps are separately proved.
3. The required irreducibility is analytic irreducibility of
   `sourceComplexGramVariety d n`, obtained from the symmetric determinantal
   variety identification.  No extra ad hoc hypothesis saying that `U` lies in a
   chosen component should be added to the theorem-2 API: for an irreducible
   analytic space, any nonempty relatively open subdomain inherits the relevant
   irreducible identity principle.  Here nonemptiness of `U` follows from
   `hW_ne` and `hW_sub`.
4. These analytic-variety facts are now proved in Lean through the checked
   local-basis, connected regular-locus, and dense rank-exact extension
   theorems in `SourceComplexDensity.lean` and `SourceComplexSchurGraph.lean`.
   They must remain proved theorems, not be replaced by a production axiom or a
   new `sorry`.

This is the exact point at which Hall-Wightman's scalar-product variety theorem
enters the Lean proof.  The checked implementation realizes the required
scalar-product-variety continuation content by local Schur charts, connected
rank-exact neighborhoods, rank-exact propagation, and dense extension to the
singular locus.  It is not sound to replace this chain by connectedness alone.

```lean

theorem BHW.sourceDistributionalUniquenessSetOnVariety_of_realEnvironment
    [NeZero d]
    (n : ℕ)
    {O : Set (Fin n -> Fin n -> ℝ)}
    (hO_env : BHW.IsHWRealEnvironment d n O) :
    BHW.sourceDistributionalUniquenessSetOnVariety d n O := by
  refine ⟨hO_env.nonempty, ?_⟩
  intro U Φ Ψ hU_rel hU_conn hO_sub hΦ hΨ h_eq
  let H : (Fin n -> Fin n -> ℂ) -> ℂ := fun Z => Φ Z - Ψ Z
  have hH : BHW.SourceVarietyHolomorphicOn d n H U :=
    BHW.SourceVarietyHolomorphicOn.sub
      (d := d) (n := n) hΦ hΨ
  have hO_zero :
      ∀ G ∈ O, H (BHW.sourceRealGramComplexify n G) = 0 := by
    intro G hG
    dsimp [H]
    exact sub_eq_zero.mpr (h_eq G hG)
  obtain ⟨W, hW_rel, hW_ne, hW_sub, hW_eq⟩ :=
    BHW.sourceVariety_localChart_totallyReal_zero
      (d := d) (n := n) hO_env hU_rel hO_sub hH hO_zero
  have hzeroU : Set.EqOn H 0 U :=
    BHW.sourceComplexGramVariety_identity_principle
      (d := d) (n := n) hU_rel hU_conn hW_rel hW_ne hW_sub
      hH hW_eq
  intro Z hZ
  exact sub_eq_zero.mp (hzeroU hZ)
```

This theorem is now checked in
`BHWPermutation/SourceDistributionalUniqueness.lean`.  The file is deliberately
downstream of `SourceExtension.lean` to avoid an import cycle: it imports the
local totally-real zero theorem and the checked source-complex identity
principle, then proves the uniqueness predicate by the direct
`H := Φ - Ψ` argument above.

The conversion from this base adjacent package to the permutation-indexed
`SourceDistributionalAdjacentTubeAnchor` is pure bookkeeping and is now
implemented as
`bvt_F_distributionalJostAnchor_of_selectedJostData` in
`OSToWightmanSelectedWitness.lean`.  The source file's `compact_branch_eq` quantifies
over `SchwartzMap (Fin n -> Fin (d + 1) -> ℝ) ℂ`; after importing the
reconstruction layer this is definitionally the same test-function carrier as
`SchwartzNPoint d n = SchwartzMap (NPointDomain d n) ℂ`, with
`NPointDomain d n = Fin n -> Fin (d + 1) -> ℝ`.

```lean
private def realPerm (π : Equiv.Perm (Fin n))
    (x : NPointDomain d n) : NPointDomain d n :=
  fun k => x (π k)

private theorem continuous_realPerm (π : Equiv.Perm (Fin n)) :
    Continuous (realPerm (d := d) π) := by
  apply continuous_pi
  intro k
  exact continuous_apply (π k)

def bvt_F_distributionalJostAnchor_of_selectedJostData
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n) :
    SourceDistributionalAdjacentTubeAnchor
      (d := d) n (bvt_F OS lgc n) := by
  refine
    { realPatch := ?realPatch
      realPatch_open := ?realPatch_open
      realPatch_nonempty := ?realPatch_nonempty
      realPatch_jost := ?realPatch_jost
      realPatch_left_sector := ?realPatch_left_sector
      realPatch_right_sector := ?realPatch_right_sector
      gramEnvironment := ?gramEnvironment
      gramEnvironment_unique := ?gramEnvironment_unique
      gram_left_mem := ?gram_left_mem
      gram_environment_realized := ?gram_environment_realized
      gram_right_eq_perm_left := ?gram_right_eq_perm_left
      compact_branch_eq := ?compact_branch_eq }
  · exact fun π i hi => {x | realPerm (d := d) π x ∈ hData.basePatch i hi}
  · intro π i hi
    exact (hData.basePatch_open i hi).preimage (continuous_realPerm (d := d) π)
  · intro π i hi
    rcases hData.basePatch_nonempty i hi with ⟨y, hy⟩
    refine ⟨realPerm (d := d) π.symm y, ?_⟩
    have hperm :
        realPerm (d := d) π (realPerm (d := d) π.symm y) = y := by
      ext k μ
      simp [realPerm]
    simpa [hperm] using hy
  · intro π i hi x hx
    have hy := hData.basePatch_jost i hi (realPerm (d := d) π x) hx
    simpa [realPerm] using
      BHW.jostSet_permutation_invariant (d := d) (n := n) π.symm hy
  · intro π i hi x hx
    have hy := hData.basePatch_left_ET i hi (realPerm (d := d) π x) hx
    simpa [BHW.permutedExtendedTubeSector, realPerm] using hy
  · intro π i hi x hx
    have hy :=
      hData.basePatch_right_ET i hi (realPerm (d := d) π x) hx
    simpa [BHW.permutedExtendedTubeSector, realPerm, Equiv.Perm.mul_apply]
      using hy
  · exact fun _π i hi => hData.baseGramEnvironment i hi
  · exact fun _π i hi => hData.baseGramEnvironment_unique i hi
  · intro π i hi x hx
    simpa [realPerm] using
      hData.baseGram_left_mem i hi (realPerm (d := d) π x) hx
  · intro π i hi G hG
    rcases hData.baseGram_realized i hi G hG with ⟨y, hy, hG_y⟩
    refine ⟨realPerm (d := d) π.symm y, ?_, ?_⟩
    · have hperm :
          realPerm (d := d) π (realPerm (d := d) π.symm y) = y := by
        ext k μ
        simp [realPerm]
      simpa [hperm] using hy
    · simpa [realPerm] using hG_y
  · intro π i hi x hx
    ext a b
    simp [BHW.sourceRealMinkowskiGram, BHW.sourcePermuteGram,
      Equiv.Perm.mul_apply]
  · intro π i hi φ hφ_compact hφ_tsupport
    let τ : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
    let ψ : SchwartzNPoint d n :=
      BHW.permuteSchwartz (d := d) π.symm φ
    have hψ_compact :
        HasCompactSupport (ψ : NPointDomain d n -> ℂ) :=
      BHW.permuteSchwartz_hasCompactSupport (d := d) π.symm φ
        (by simpa using hφ_compact)
    have hψ_tsupport :
        tsupport (ψ : NPointDomain d n -> ℂ) ⊆ hData.basePatch i hi := by
      intro y hy
      have hyφ :
          realPerm (d := d) π.symm y ∈
            tsupport (φ : NPointDomain d n -> ℂ) := by
        have hsupp_eq :=
          BHW.tsupport_permuteSchwartz (d := d) π.symm φ
        rw [show ψ = BHW.permuteSchwartz (d := d) π.symm φ from rfl] at hy
        rw [hsupp_eq] at hy
        simpa [realPerm] using hy
      have hxPatch :
          realPerm (d := d) π
              (realPerm (d := d) π.symm y) ∈
            hData.basePatch i hi :=
        hφ_tsupport hyφ
      have hperm :
          realPerm (d := d) π (realPerm (d := d) π.symm y) = y := by
        ext k μ
        simp [realPerm]
      simpa [hperm] using hxPatch
    have hbase :=
      hData.baseCompactEq i hi ψ hψ_compact hψ_tsupport
    have hleft :
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (fun k => BHW.realEmbed x (π k)) * φ x) =
          ∫ y : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed y) * ψ y := by
      simpa [ψ, realPerm] using
        BHW.integral_perm_eq_self (d := d) (n := n) π
          (fun y : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed y) * ψ y)
    have hright :
        (∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (fun k => BHW.realEmbed x ((π * τ) k)) * φ x) =
          ∫ y : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => y (τ k))) * ψ y := by
      simpa [ψ, realPerm, τ, Equiv.Perm.mul_apply] using
        BHW.integral_perm_eq_self (d := d) (n := n) π
          (fun y : NPointDomain d n =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed (fun k => y (τ k))) * ψ y)
    exact hleft.trans (hbase.trans hright.symm)
```

The support proof above is the required one: rewrite
`tsupport (BHW.permuteSchwartz π.symm φ)` by
`BHW.tsupport_permuteSchwartz`, apply the original
`hφ_tsupport`, and simplify the two inverse coordinate permutations.  The Lean
pass must not add an extra support hypothesis.

In the current Lean representation, `S''_n` is covered by the sectors
`BHW.permutedExtendedTubeSector d n π`; the checked cover facts are
`BHW.mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube`,
`BHW.permutedExtendedTube_eq_iUnion_sectors`, and
`BHW.permutedExtendedTubeSector_subset_permutedExtendedTube`.

Exact proof transcript for the replacement:

1. prove the three elementary private `S'_n` datum lemmas:
   `source_permutedForwardBranch_holomorphicOn`,
   `source_permutedForwardBranch_restrictedLorentzInvariant`, and
   `source_permutedForwardBranch_symmetric`;
2. inside the generic theorem, derive the ordinary forward-tube
   complex-Lorentz overlap invariance by the checked Hall-Wightman core lemma:
   `BHW.complex_lorentz_invariance n F hF_holo hF_lorentz`;
3. use that derived overlap invariance only for the local `extendF` API, for
   example `BHW.extendF_holomorphicOn`; do not make it a source hypothesis;
4. define the sector branch family
   `G π z := BHW.extendF F (fun k => z (π k))`;
5. use `BHW.extendF_holomorphicOn` and the coordinate-permutation map to show
   each `G π` is holomorphic on
   `BHW.permutedExtendedTubeSector d n π`.  This support step is now the
   Lean theorem
   `BHW.permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz` in
   `BHWPermutation/SourceExtension.lean`;
6. the hard Hall-Wightman source step is exactly the compatibility theorem
   `hallWightman_source_permutedBranch_compatibility`: if one point lies in
   two explicit PET sectors, the two `G` branches have the same value;

   This is a genuine Hall-Wightman compatibility step, not a shortcut from the
   raw formula `hF_perm`.  If `z` lies in two PET sectors, the two branch values
   are obtained by choosing complex-Lorentz representatives of
   `(fun k => z (π k))` and `(fun k => z (ρ k))` in the base extended tube.
   The point produced after permuting one representative and transporting it by
   the other complex Lorentz transform need not lie in `BHW.ForwardTube d n`.
   Therefore the ordinary forward-tube invariance of `F`, even combined with
   pointwise permutation symmetry, does not by itself prove all-sector branch
   equality.  The source input must be Hall-Wightman's one-function
   single-valued continuation for the Euclidean-anchored symmetric
   permuted-tube datum on `S'_n`, enlarged to `S''_n`.

   Lean-shaped form of the exact source obligation:

   ```lean
   let G : (π : Equiv.Perm (Fin n)) ->
       (Fin n -> Fin (d + 1) -> ℂ) -> ℂ :=
     fun π z => BHW.extendF F (fun k => z (π k))
   have hG_holo :
       ∀ π, DifferentiableOn ℂ (G π)
         (BHW.permutedExtendedTubeSector d n π) :=
     fun π =>
       BHW.permutedExtendF_holomorphicOn_sector_of_forwardTube_lorentz
         (d := d) n F hF_holo hF_lorentz π
   -- Hall-Wightman source step, not supplied by `gluedPETValue`:
   have hcompat :
       ∀ π ρ z,
         z ∈ BHW.permutedExtendedTubeSector d n π ->
         z ∈ BHW.permutedExtendedTubeSector d n ρ ->
         G π z = G ρ z :=
     hallWightman_source_permutedBranch_compatibility
       (d := d) hd n F hF_holo hF_lorentz hF_perm hAnchor
   refine ⟨BHW.gluedPETValue (d := d) (n := n) G, ?_, ?_⟩
   · exact BHW.gluedPETValue_holomorphicOn
       (d := d) (n := n) G hG_holo hcompat
   · intro π z hzπ
     exact BHW.gluedPETValue_eq_of_mem_sector
       (d := d) (n := n) G hcompat π z hzπ
   ```

   The final Lean theorem
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`
   should be the mechanical gluing proof above after the source compatibility
   theorem has been supplied.  The theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` then consumes
   the public branch law and proves the forward-tube agreement,
   complex-Lorentz invariance, and permutation invariance outputs.
7. derive
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` from that
   branch law by the two-line `Fpet` comparison above;
8. supply `hF_holo` from `bvt_F_holomorphic`;
9. supply `hF_lorentz` from
   `bvt_F_restrictedLorentzInvariant_forwardTube`;
10. supply the distributional Euclidean/Jost anchor from
   `bvt_F_distributionalJostAnchor_of_OSII`;
11. supply `hF_perm` from `bvt_F_perm` only as auxiliary formal branch-family
   symmetry where retained by the generic API;
12. specialize the corrected generic equality theorem to any common sector point `z` and labels
   `π`, `ρ`;
13. rewrite `bvt_selectedPETBranch` to the displayed `BHW.extendF` expression
   used by Slot 7.

The local helper `BHW.gluedPETValue` is downstream packaging only.  Its theorem
`BHW.gluedPETValue_holomorphicOn` assumes all-sector compatibility
`hcompat`; it does not prove the Hall-Wightman single-valuedness theorem.
After the source compatibility theorem has supplied all-sector branch equality,
`gluedPETValue` is used to name the resulting `Fpet`, but it is not the
analytic input.

Lean implementation packet for the next pass:

1. Keep the pure source theorem in the already-created small file:
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtension.lean`.
   Do not place it in `BHWPermutation/PermutationFlow.lean`; that file contains
   circular theorem surfaces used only as historical infrastructure.
2. The current imports for this file are:

```lean
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvarianceCore
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeGluing
import OSReconstruction.ComplexLieGroups.JostPoints
```

   The implementation must not import `BHWPermutation.PermutationFlow` to get
   the source theorem.
3. The exact verification sequence for this packet is:

```bash
lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtension.lean
lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation.lean
```

Allowed local support in `SourceExtension.lean`:

1. `BHW.complex_lorentz_invariance`, derived from `hF_holo` and
   `hF_lorentz`;
2. `BHW.extendF_eq_on_forwardTube`, `BHW.extendF_preimage_eq`,
   `BHW.extendF_complex_lorentz_invariant`, and `BHW.extendF_holomorphicOn`;
3. the PET cover and topology facts
   `BHW.isOpen_permutedExtendedTube`,
   `BHW.isOpen_permutedExtendedTubeSector`,
   `BHW.permutedExtendedTubeSector_subset_permutedExtendedTube`,
   `BHW.permutedExtendedTube_eq_iUnion_sectors`, and
   `BHW.isConnected_permutedExtendedTube`;
4. `BHW.gluedPETValue` and its lemmas only after the source theorem has already
   supplied the branch law/compatibility.

Forbidden support in `SourceExtension.lean`:

1. `BHW.bargmann_hall_wightman_theorem` and any theorem named
   `bargmann_hall_wightman` in `PermutationFlow.lean`, because the current
   statement takes `hF_local_dist : IsLocallyCommutativeWeak d W`;
2. private helpers in `PermutationFlow.lean` whose hypotheses include
   `W`, `hF_bv_dist`, or `hF_local_dist`, including
   `fullExtendF_well_defined`, `F_permutation_invariance`,
   `iterated_eow_permutation_extension`, and `eow_chain_adj_swap`;
3. `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`,
   because it belongs to the archived graph route and assumes exactly the
   all-sector branch independence that the source theorem is meant to supply.

The only allowed theorem-level frontier in this new file is the
Euclidean-anchored source compatibility theorem
`BHW.hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
(or an OS-specific theorem that internally supplies the same anchor).  The old
hF_perm-only source statement has now been refactored out of the public
frontier and must not be revived as the theorem to close.  The theorem
`BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` is the planned
assembly theorem from a corrected branch law, and
`BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` must remain a
mechanical corollary, not a second analytic `sorry`.

This input order is deliberate.  Hall-Wightman starts from a function analytic
in the tube and invariant under the real orthochronous Lorentz group, then
supplies the single-valued complex-Lorentz continuation to the extended tube.
The local theorem
`bvt_F_complexLorentzInvariant_forwardTube` remains useful checked support, but
it is not the source contract for Slot 6 and should not replace the
restricted-real Lorentz hypothesis in the generic theorem statement.

Source-audit anchors:

1. OS I §4.5 first obtains a symmetric analytic datum on the permuted tube
   family `S'_n` from the Euclidean symmetry and the construction formulas.
   It then says that, using Bargmann-Hall-Wightman, this datum allows a
   single-valued symmetric `L_+(ℂ)`-invariant analytic continuation into
   `S''_n`, and only after that invokes Jost p. 83 for locality.
2. Hall-Wightman's Lemma/Theorem I starts with analyticity in the tube and
   invariance under the real orthochronous Lorentz group.  It proves that the
   relation `f(Az) = f(z)` defines a single-valued analytic continuation to
   the extended tube.
3. Therefore the active source frontier is the branch law for the branch family
   `F_π z = F (fun k => z (π k))`, but the source audit rules out the
   hF_perm-only generic version as a final theorem.  Symmetry of the
   `S'_n` datum must be anchored on the Euclidean/Jost uniqueness set where
   the OS-II Schwinger construction identifies the branch boundary values and
   supplies Schwinger permutation symmetry.  Hall-Wightman then supplies the
   single-valuedness on `S''_n`.
4. If the eventual internal proof is organized in a more literal
   family-indexed form, that helper should stay private or source-facing; the
   theorem-2 consumer should still see the one-function theorem displayed
   above.

Non-circularity requirements:

1. this theorem must not call any existing theorem whose hypotheses include
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)`;
2. in particular, the current generic theorem surfaces named
   `bargmann_hall_wightman` and `BHW.bargmann_hall_wightman_theorem` are not
   acceptable as Slot-6 inputs in their current form: the repo statements take
   `hF_local_dist : IsLocallyCommutativeWeak d W`, which is circular for
   theorem 2;
3. Streater-Wightman Theorem 3-6 is forbidden here for the same reason;
4. the allowed source input is Hall-Wightman/BHW single-valued continuation,
   with the OS-II-corrected `bvt_F` construction providing the analytic datum.

The rest of this section archives the rejected fixed-forward-tube packet so
that future work does not accidentally revive it as a theorem-2 target.

External source ledger for this slot:

1. OS I §4.5 gives the route order explicitly. In the local OCR of
   `references/Reconstruction theorem I.pdf`, the locality paragraph says:
   - "Using the Bargmann Hall Wightman theorem, [10], we conclude that ..."
   - "Now we use a theorem in Ref. [12] (p. 83, second theorem) ..."
   So the order is fixed: BHW enlargement first, Jost boundary theorem later.
2. Ref. [10] in the same bibliography is:
   Hall, D.; Wightman, A.S.,
   "A theorem on invariant analytic functions with applications to
   relativistic quantum field theory",
   Mat.-Fys. Medd. Danske Vid. Selsk. 31, no. 5 (1951).
3. Ref. [12] is:
   Jost, R., *The general theory of quantized fields*, Amer. Math. Soc. Publ.
   (1965), and OS I cites specifically p. 83, second theorem.
4. Therefore:
   - active Slot 6 consumes only the source-backed BHW single-valued
     continuation side coming from [10], after the OS-II-corrected symmetric
     analytic datum has been constructed;
   - Slot 10 is where the cited Jost boundary theorem from Ref. [12], p. 83,
     second theorem, is consumed.
5. The former candidate Slot-6 derived theorem
   `hallWightman_fixedPoint_endpointActiveGallery_of_two_le` is rejected for
   theorem 2 in its documented form. It required common fixed-`w`
   `PermutedForwardTube` slice witnesses, but distinct permuted forward-tube
   sectors are disjoint in the local Lean definitions.
6. More precisely, the exported chain theorem `petOrbitChamberChain_of_two_le`
   is not a verbatim numbered theorem from OS I, and the documented common
   forward-tube-slice version should not be introduced as a theorem-2 frontier.
   If a future non-theorem-2 geometry project wants a fixed-fiber graph theorem,
   it must be restated using extended-tube sector membership, not common
   forward-tube overlap.
7. The support objects `ActivePETOrbitLabel`, `activePETOrbitAdj`,
   `one_mem_activePETOrbitLabel_of_forwardTube`,
   `sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube`, and
   `activePETOrbitAdj_implies_petOrbitChamberAdjStep` are archived
   fixed-`w` experiments.  They are not Slot-6 theorem-2 proof language unless
   a future route restates the geometry in extended-tube sector terms and
   passes a fresh source audit.
8. The theorem-2-facing consumer after Slot 6 is now the OS specialization
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`, supplied by the
   direct source-backed BHW single-valuedness theorem.  The selected-adjacent
   monodromy consumer
   `bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData` remains
   checked conditional infrastructure with an explicit `hOrbit` hypothesis.

Archived rejected fixed-forward-tube packet:

```lean
def ActivePETOrbitLabel
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :=
  {σ : Equiv.Perm (Fin n) // (permLambdaSlice (d := d) n σ w).Nonempty}

def activePETOrbitAdj
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    ActivePETOrbitLabel d n w -> ActivePETOrbitLabel d n w -> Prop :=
  fun a b =>
    ∃ (i : Fin n) (hi : i.val + 1 < n),
      b.1 = a.1 * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      ((permLambdaSlice (d := d) n a.1 w) ∩
        (permLambdaSlice (d := d) n b.1 w)).Nonempty

def one_mem_activePETOrbitLabel_of_forwardTube
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (hw : w ∈ BHW.ForwardTube d n) :
    ActivePETOrbitLabel d n w

def sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (hΛ : BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ) :
    ActivePETOrbitLabel d n w

theorem activePETOrbitAdj_implies_petOrbitChamberAdjStep
    (w : Fin n -> Fin (d + 1) -> ℂ)
    {a b : ActivePETOrbitLabel d n w}
    (hab : activePETOrbitAdj d n w a b) :
    PETOrbitChamberAdjStep d n w a.1 b.1

structure PETOrbitChamberChain
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (σ : Equiv.Perm (Fin n)) where
  m : ℕ
  τ : Fin (m + 1) -> Equiv.Perm (Fin n)
  hstart : τ 0 = 1
  hend : τ ⟨m, Nat.lt_succ_self m⟩ = σ
  hstep :
    ∀ j : Fin m,
      ∃ (i : Fin n) (hi : i.val + 1 < n) (Λj : ComplexLorentzGroup d),
        τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩ =
          τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩ * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
        BHW.complexLorentzAction Λj w ∈
          BHW.PermutedForwardTube d n (τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩) ∧
        BHW.complexLorentzAction Λj w ∈
          BHW.PermutedForwardTube d n
            (τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩)

def PETOrbitChamberAdjStep
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    Equiv.Perm (Fin n) -> Equiv.Perm (Fin n) -> Prop :=
  fun π ρ =>
    ∃ (i : Fin n) (hi : i.val + 1 < n) (Λj : ComplexLorentzGroup d),
      ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      BHW.complexLorentzAction Λj w ∈ BHW.PermutedForwardTube d n π ∧
      BHW.complexLorentzAction Λj w ∈ BHW.PermutedForwardTube d n ρ

theorem petOrbitChamberChain_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ BHW.ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ ->
        PETOrbitChamberChain d n w σ

lemma mem_permForwardOverlapIndexSet_of_fixedPoint
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {w : Fin n -> Fin (d + 1) -> ℂ}
    (hw : w ∈ BHW.ForwardTube d n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ) :
    Λ ∈ BHW.permForwardOverlapIndexSet (d := d) n σ

noncomputable def PETOrbitChamberChain.ofReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (h :
      Relation.ReflTransGen
        (PETOrbitChamberAdjStep d n w)
        (1 : Equiv.Perm (Fin n)) σ) :
    PETOrbitChamberChain d n w σ

theorem PETOrbitChamberChain.toReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (chain : PETOrbitChamberChain d n w σ) :
    Relation.ReflTransGen
      (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
      (1 : Equiv.Perm (Fin n)) σ

theorem petOrbitChamberConnected_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ BHW.ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ ->
        Relation.ReflTransGen
          (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ
```

Archived interpretation:

1. `ActivePETOrbitLabel`, `activePETOrbitAdj`, and `PETOrbitChamberChain`
   record the rejected fixed-forward-tube packet.
2. `hallWightman_fixedPoint_endpointActiveGallery_of_two_le`,
   `petOrbitChamberChain_of_two_le`, and any theorem using
   `activePETOrbitAdj` as a common-slice edge are not active theorem-2
   surfaces.  The reachable-label theorem
   `petOrbitChamberConnected_of_two_le` remains a conditional monodromy
   theorem only in the `BHW.petReachableLabelAdjStep` form stated above.
3. The reason is not merely missing documentation: the common-slice edge
   required by this packet would put one point in two distinct permuted forward
   tubes, contradicting `BHW.permutedForwardTube_sector_eq_of_mem`.
4. These names may remain in experimental geometry files, but strict theorem 2
   should move through the source-backed
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` packet and
   the OS specialization
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.

The older surface `bhw_fixedPoint_chamberAdjacency_connected_of_two_le` is
quarantined as a diagnostic-only corollary outside theorem 2.

Archived fixed-forward-tube implementation status:

Implemented support in `PETOrbitChamberChain.lean` currently includes
`permLambdaSlice`, `mem_permLambdaSlice_iff`,
`permLambdaSlice_eq_orbitSet`,
`mem_petReachableLabelSet_iff_nonempty_permLambdaSlice`,
`ActivePETOrbitLabel`, `activePETOrbitAdj`,
`one_mem_activePETOrbitLabel_of_forwardTube`,
`sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube`,
`PETOrbitChamberAdjStep`,
`petOrbitChamberAdjStep_iff_exists_slice_overlap`,
`activePETOrbitAdj_implies_petOrbitChamberAdjStep`,
`PETOrbitChamberChain`, `mem_permForwardOverlapIndexSet_of_fixedPoint`,
`PETOrbitChamberChain.toReflTransGen`, and
`PETOrbitChamberChain.ofReflTransGen`.

The following theorem surfaces are archived and should not be implemented for
theorem 2:
`hallWightman_fixedPoint_endpointActiveGallery_of_two_le`,
`hallWightman_fixedPoint_adjacentChainData_of_two_le`,
`petOrbitChamberChain_of_two_le`,
`petOrbitChamberConnected_of_two_le`.

Quarantined diagnostic-only corollary, not in the current implementation gate:
`bhw_fixedPoint_chamberAdjacency_connected_of_two_le`.

The inventory below is therefore an archived diagnostic inventory, not a target
inventory and not a statement that every displayed theorem is already exported
by the current Lean files:

```lean
theorem permForwardOverlap_connected_nontrivial
    [NeZero d]
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : σ ≠ 1) (hn : ¬ n <= 1) :
    IsConnected (BHW.permForwardOverlapSet (d := d) n σ)

def ActivePETOrbitLabel
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :=
  {σ : Equiv.Perm (Fin n) // (permLambdaSlice (d := d) n σ w).Nonempty}

def activePETOrbitAdj
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    ActivePETOrbitLabel d n w -> ActivePETOrbitLabel d n w -> Prop :=
  fun a b =>
    ∃ (i : Fin n) (hi : i.val + 1 < n),
      b.1 = a.1 * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      ((permLambdaSlice (d := d) n a.1 w) ∩
        (permLambdaSlice (d := d) n b.1 w)).Nonempty

def one_mem_activePETOrbitLabel_of_forwardTube
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (hw : w ∈ BHW.ForwardTube d n) :
    ActivePETOrbitLabel d n w

def sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (hΛ : BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ) :
    ActivePETOrbitLabel d n w

theorem activePETOrbitAdj_implies_petOrbitChamberAdjStep
    (w : Fin n -> Fin (d + 1) -> ℂ)
    {a b : ActivePETOrbitLabel d n w}
    (hab : activePETOrbitAdj d n w a b) :
    PETOrbitChamberAdjStep d n w a.1 b.1

lemma mem_permForwardOverlapIndexSet_of_fixedPoint
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {w : Fin n -> Fin (d + 1) -> ℂ}
    (hw : w ∈ BHW.ForwardTube d n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ) :
    Λ ∈ BHW.permForwardOverlapIndexSet (d := d) n σ

theorem petOrbitChamberChain_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ BHW.ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ ->
        PETOrbitChamberChain d n w σ

noncomputable def PETOrbitChamberChain.ofReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (h :
      Relation.ReflTransGen
        (PETOrbitChamberAdjStep d n w)
        (1 : Equiv.Perm (Fin n)) σ) :
    PETOrbitChamberChain d n w σ

theorem PETOrbitChamberChain.toReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (chain : PETOrbitChamberChain d n w σ) :
    Relation.ReflTransGen
      (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
      (1 : Equiv.Perm (Fin n)) σ

theorem petOrbitChamberConnected_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ BHW.ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ ->
        Relation.ReflTransGen
          (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ
```

The first helper is the exact blocker-to-overlap conversion, and it is now
checked as
`BHW.permForwardOverlap_connected_nontrivial`
in `PermutationFlow.lean`:

```lean
have hseed_conn :
    IsConnected (permOrbitSeedSet (d := d) n σ) := by
  simpa [permOrbitSeedSet] using
    blocker_isConnected_permSeedSet_nontrivial
      (d := d) n σ hσ hn
have hFwd_conn :
    IsConnected (BHW.permForwardOverlapSet (d := d) n σ) :=
  (isConnected_permOrbitSeedSet_iff_permForwardOverlapSet
    (d := d) n σ).1 hseed_conn
```

Verified status:

- this first helper is genuinely dimension-agnostic;
- it is a checked auxiliary BHW theorem;
- it is **not** itself the Slot-6 theorem that theorem 2 consumes.

Critical audit result:

- `permForwardOverlapSet (d := d) n σ` is a set of **points `w`** in the
  forward tube satisfying `σ · w ∈ ET`;
- but the monodromy target
  `petReachableLabelAdjStep ... w`
  is about a **fixed forward-tube point `w`** and varying Lorentz transforms
  `Λ` with `Λ · w` in successive permuted forward-tube chambers;
- so a theorem phrased only in terms of
  `IsConnected (permForwardOverlapSet (d := d) n σ)`
  is not yet the right theorem surface for Slot 6.

The genuine fixed-`w` geometry object is the chamber slice

```lean
def permLambdaSlice
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    Set (ComplexLorentzGroup d) :=
  {Λ : ComplexLorentzGroup d |
    BHW.complexLorentzAction Λ (BHW.permAct (d := d) σ w) ∈
      BHW.ForwardTube d n}
```

and the exact fixed-`w` identity is

```lean
lemma mem_permLambdaSlice_iff
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (Λ : ComplexLorentzGroup d) :
    Λ ∈ permLambdaSlice (d := d) n σ w ↔
      BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ := by
  simpa [permLambdaSlice, BHW.PermutedForwardTube, BHW.permAct,
    BHW.lorentz_perm_commute]

theorem mem_petReachableLabelSet_iff_nonempty_permLambdaSlice
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ BHW.petReachableLabelSet (d := d) (n := n) w ↔
      (permLambdaSlice (d := d) n σ w).Nonempty := by
  rw [BHW.mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube]
  constructor
  · rintro ⟨Λ, hΛ⟩
    exact ⟨Λ, (mem_permLambdaSlice_iff (d := d) n σ w Λ).mpr hΛ⟩
  · rintro ⟨Λ, hΛ⟩
    exact ⟨Λ, (mem_permLambdaSlice_iff (d := d) n σ w Λ).mp hΛ⟩

theorem petOrbitChamberAdjStep_iff_exists_slice_overlap
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (π ρ : Equiv.Perm (Fin n)) :
    BHW.PETOrbitChamberAdjStep d n w π ρ ↔
      ∃ (i : Fin n) (hi : i.val + 1 < n),
        ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
        ((permLambdaSlice (d := d) n π w) ∩
          (permLambdaSlice (d := d) n ρ w)).Nonempty := by
  constructor
  · rintro ⟨i, hi, Λj, hρ, hπ, hρmem⟩
    refine ⟨i, hi, hρ, ?_⟩
    refine ⟨Λj, ?_, ?_⟩
    · exact (mem_permLambdaSlice_iff (d := d) n π w Λj).mpr hπ
    · exact (mem_permLambdaSlice_iff (d := d) n ρ w Λj).mpr hρmem
  · rintro ⟨i, hi, hρ, ⟨Λj, hπ, hρmem⟩⟩
    refine ⟨i, hi, Λj, hρ, ?_, ?_⟩
    · exact (mem_permLambdaSlice_iff (d := d) n π w Λj).mp hπ
    · exact (mem_permLambdaSlice_iff (d := d) n ρ w Λj).mp hρmem
```

So the correct fixed-`w` chamber index slice is

```lean
{Λ : ComplexLorentzGroup d |
  BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ}
```

which is equivalent, by `lorentz_perm_commute`, to the fixed-`w` version of the
`d = 1` object already formalized in `IndexSetD1.lean` as
`permLambdaSliceD1`.

This fixed-`w` slice language is archived for theorem 2.  It records why the
old route was tempting, but the common-slice edge below is incompatible with
permuted-forward-tube disjointness.  The reachable-label `hOrbit` theorem
feeding the checked BHW/PET monodromy consumer is also conditional
infrastructure; it is not the strict OS-paper Slot-6 gate.

The checked reduction chain in `PermutedTubeMonodromy.lean` is:

```lean
theorem petReachableLabelSet_adjacent_connected_of_orbitChamberConnected
theorem petSectorFiber_adjacent_connected_of_reachableLabelConnected
theorem extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected
```

This checked reduction chain is a conditional Lean interface.  A proof using it
would have to supply the concrete `hOrbit` hypothesis consumed by
`extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`; the
strict theorem-2 route instead uses the direct source-backed BHW
single-valuedness theorem.  Do not bypass either route by using the
locality-assuming top-level `BHW.bargmann_hall_wightman_theorem`.

If pursued as a separate conditional lane, `hOrbit` must accomplish the
following mathematically: for fixed `w` and an endpoint
`Λ · w` lying in the permuted forward-tube chamber `σ`, build a finite chamber
chain

```lean
1 = τ₀, τ₁, ..., τₘ = σ
```

such that every `τj` is reachable from the same fixed point `w`, and
successive labels differ by an adjacent transposition.  The endpoint witness
`Λ` only proves that `σ` is reachable; it is not used as a common witness for
every intermediate label.  Each adjacent pair gives one
`BHW.petReachableLabelAdjStep`, and the finite chain is packaged as
`Relation.ReflTransGen`.

Important negative check.  A common Lorentz witness for two ordinary permuted
forward-tube chambers is impossible unless the labels are equal:

```lean
lemma permLambdaSlice_inter_nonempty_forces_eq
    (w : Fin n -> Fin (d + 1) -> ℂ)
    {π ρ : Equiv.Perm (Fin n)}
    (h :
      ((permLambdaSlice (d := d) n π w) ∩
        (permLambdaSlice (d := d) n ρ w)).Nonempty) :
    π = ρ := by
  rcases h with ⟨Λ, hπ, hρ⟩
  exact
    BHW.permutedForwardTube_sector_eq_of_mem
      (d := d) (n := n) π ρ
      ((mem_permLambdaSlice_iff (d := d) n π w Λ).mp hπ)
      ((mem_permLambdaSlice_iff (d := d) n ρ w Λ).mp hρ)
```

Therefore any conditional reachable-label edge relation cannot be a
common-slice-overlap relation.  It must be the checked relation

```lean
BHW.petReachableLabelAdjStep (d := d) (n := n) w π ρ
```

whose data are only: `ρ = π * adjacentSwap`, `π` is reachable, and `ρ` is
reachable.

So the exact theorem order for that conditional monodromy lane is:

```lean
def ActivePETOrbitLabel
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :=
  {σ : Equiv.Perm (Fin n) // (permLambdaSlice (d := d) n σ w).Nonempty}

def activePETOrbitAdj
    (d n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    ActivePETOrbitLabel d n w -> ActivePETOrbitLabel d n w -> Prop :=
  fun a b =>
    ∃ (i : Fin n) (hi : i.val + 1 < n),
      b.1 = a.1 * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      ((permLambdaSlice (d := d) n a.1 w) ∩
        (permLambdaSlice (d := d) n b.1 w)).Nonempty

def one_mem_activePETOrbitLabel_of_forwardTube
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (hw : w ∈ ForwardTube d n) :
    ActivePETOrbitLabel d n w

def sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ) :
    ActivePETOrbitLabel d n w

theorem activePETOrbitAdj_implies_petOrbitChamberAdjStep
    (w : Fin n -> Fin (d + 1) -> ℂ)
    {a b : ActivePETOrbitLabel d n w}
    (hab : activePETOrbitAdj d n w a b) :
    PETOrbitChamberAdjStep d n w a.1 b.1

lemma mem_permForwardOverlapIndexSet_of_fixedPoint
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {w : Fin n -> Fin (d + 1) -> ℂ}
    (hw : w ∈ ForwardTube d n)
    {Λ : ComplexLorentzGroup d}
    (hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ) :
    Λ ∈ permForwardOverlapIndexSet (d := d) n σ
theorem petOrbitChamberChain_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        PETOrbitChamberChain d n w σ
noncomputable def PETOrbitChamberChain.ofReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (h :
      Relation.ReflTransGen
        (PETOrbitChamberAdjStep d n w)
        (1 : Equiv.Perm (Fin n)) σ) :
    PETOrbitChamberChain d n w σ
theorem PETOrbitChamberChain.toReflTransGen
    {w : Fin n -> Fin (d + 1) -> ℂ}
    {σ : Equiv.Perm (Fin n)}
    (chain : PETOrbitChamberChain d n w σ) :
    Relation.ReflTransGen
      (petReachableLabelAdjStep (d := d) (n := n) w)
      (1 : Equiv.Perm (Fin n)) σ
theorem petOrbitChamberConnected_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        Relation.ReflTransGen
          (petReachableLabelAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ
```

Conditional transcript for `petOrbitChamberConnected_of_two_le`:

This section is retained only to make the checked monodromy consumer honest.
It is **not** the strict OS theorem-2 implementation gate.  A proof of this
theorem would be a separate pointwise complex-Lorentz-orbit stratification
result; it cannot be cited as "the Hall-Wightman theorem" unless it is first
proved from, or explicitly derived as a corollary of, the source-backed
single-valuedness theorem on `S''_n`.

1. First prove endpoint membership in the reachable-label set.

   ```lean
   have hOne :
       (1 : Equiv.Perm (Fin n)) ∈
         BHW.petReachableLabelSet (d := d) (n := n) w :=
     BHW.one_mem_petReachableLabelSet_of_forwardTube (d := d) (n := n) hw
   have hSigma :
       σ ∈ BHW.petReachableLabelSet (d := d) (n := n) w :=
     (BHW.mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube
       (d := d) (n := n) w σ).2 ⟨Λ, hΛ⟩
   ```

2. Use the Hall-Wightman curve construction, not a common-slice overlap, to
   connect the active chamber labels.  The pure geometry theorem to prove is:

   ```lean
   theorem BHW.petReachableLabelSet_adjacent_connected_of_HW_chamber_curve
       [NeZero d] (hd : 2 <= d) (n : ℕ)
       (w : Fin n -> Fin (d + 1) -> ℂ)
       (hw : w ∈ BHW.ForwardTube d n) :
       ∀ σ ∈ BHW.petReachableLabelSet (d := d) (n := n) w,
         Relation.ReflTransGen
           (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
           (1 : Equiv.Perm (Fin n)) σ
   ```

   This theorem would formalize a custom orbit-stratification geometry: take a
   curve in the complex Lorentz group from the identity chamber to an endpoint
   chamber, refine it to a chamber-generic finite subdivision, and record the
   permuted forward-tube chamber labels met by the fixed orbit.  This is
   stronger and more rigid than the OS/Hall-Wightman source theorem, because
   the base point `w` is not allowed to move through the real Jost
   environments used by the source proof.

3. The chamber-curve theorem must expose these internal lemmas, rather than
   hiding them behind a new axiom or a production `sorry`:

   ```lean
   structure BHW.HWChamberSubdivision
       (d n : ℕ)
       (w : Fin n -> Fin (d + 1) -> ℂ)
       (σ : Equiv.Perm (Fin n))
       (Λ : ComplexLorentzGroup d)
       (γ : C(unitInterval, ComplexLorentzGroup d)) where
     m : ℕ
     t : Fin (m + 2) -> unitInterval
     label : Fin (m + 1) -> Equiv.Perm (Fin n)
     t_strict : StrictMono t
     t_start : t 0 = 0
     t_end : t (Fin.last (m + 1)) = 1
     label_start : label 0 = 1
     label_end : label (Fin.last m) = σ
     interval_mem :
       ∀ j : Fin (m + 1),
         ∀ s : unitInterval,
           t j.castSucc < s -> s < t j.succ ->
             BHW.complexLorentzAction (γ s) w ∈
               BHW.PermutedForwardTube d n (label j)
     crossing :
       ∀ j : Fin m,
         BHW.OneAdjacentForwardConeWall d n
           (BHW.complexLorentzAction (γ (t j.succ)) w)
           (label j.castSucc) (label j.succ)

   theorem BHW.exists_HW_chamber_curve
       [NeZero d] (hd : 2 <= d) (n : ℕ)
       {w : Fin n -> Fin (d + 1) -> ℂ}
       (hw : w ∈ BHW.ForwardTube d n)
       {σ : Equiv.Perm (Fin n)} {Λ : ComplexLorentzGroup d}
       (hΛ : BHW.complexLorentzAction Λ w ∈
         BHW.PermutedForwardTube d n σ) :
       ∃ γ : C(unitInterval, ComplexLorentzGroup d),
         γ 0 = 1 ∧ γ 1 = Λ ∧
         BHW.HWChamberSubdivision d n w σ Λ γ

   theorem BHW.HWChamberSubdivision.to_adjacent_label_chain
       [NeZero d] (hd : 2 <= d) (n : ℕ)
       {w : Fin n -> Fin (d + 1) -> ℂ}
       (hw : w ∈ BHW.ForwardTube d n)
       {σ : Equiv.Perm (Fin n)} {Λ : ComplexLorentzGroup d}
       (hΛ : BHW.complexLorentzAction Λ w ∈
         BHW.PermutedForwardTube d n σ)
       {γ : C(unitInterval, ComplexLorentzGroup d)}
       (hγ : BHW.HWChamberSubdivision d n w σ Λ γ)
       (hγ0 : γ 0 = 1) (hγ1 : γ 1 = Λ) :
       Relation.ReflTransGen
         (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
         (1 : Equiv.Perm (Fin n)) σ
   ```

4. `HWChamberSubdivision.to_adjacent_label_chain` inducts over `j : Fin m`.
   For every interval label, choose a midpoint `s_j` with
   `t j.castSucc < s_j < t j.succ`; `interval_mem` gives
   `complexLorentzAction (γ s_j) w ∈ PermutedForwardTube ... (label j)`,
   hence `label j ∈ petReachableLabelSet`.  For every crossing, apply the
   local wall-crossing theorem below to `hγ.crossing j`, then append the
   corresponding `BHW.petReachableLabelAdjStep`.  The wall-crossing theorem is
   the remaining concrete geometry:

   ```lean
   def BHW.OneSidedChamberLimit
       (d n : ℕ)
       (z : Fin n -> Fin (d + 1) -> ℂ)
       (π : Equiv.Perm (Fin n)) : Prop :=
     ∃ γ : ℝ -> Fin n -> Fin (d + 1) -> ℂ,
       Tendsto γ (nhdsWithin 0 (Set.Ioi 0)) (nhds z) ∧
       ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
         γ t ∈ BHW.PermutedForwardTube d n π

   def BHW.OneAdjacentForwardConeWall
       (d n : ℕ)
       (z : Fin n -> Fin (d + 1) -> ℂ)
       (π ρ : Equiv.Perm (Fin n)) : Prop :=
     ∃ (i : Fin n) (hi : i.val + 1 < n),
       -- exactly the adjacent imaginary difference indexed by `i`
       -- is on the forward-cone boundary after reading the chamber in
       -- the `π`-coordinates; every other chamber inequality stays strict
       BHW.IsOnlyForwardConeWall d n z π i hi ∧
       BHW.CrossesThatWallTo d n z π ρ i hi

   theorem BHW.permutedForwardTube_generic_wall_crossing_adjacent
       [NeZero d] (hd : 2 <= d) (n : ℕ)
       {z : Fin n -> Fin (d + 1) -> ℂ}
       {π ρ : Equiv.Perm (Fin n)}
       (hleft : BHW.OneSidedChamberLimit d n z π)
       (hright : BHW.OneSidedChamberLimit d n z ρ)
       (hgeneric : BHW.OneAdjacentForwardConeWall d n z π ρ) :
       ∃ (i : Fin n) (hi : i.val + 1 < n),
         ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩
   ```

   This is where the finite chamber stratification must be proved.  It is not
   optional, and it must not be replaced by assuming connectedness of
   `permForwardOverlapSet` or by using a common Lorentz witness.

5. After the chamber-curve theorem is proved, the production theorem is a
   short transcript:

   ```lean
   intro w hw σ Λ hΛ
   have hσ :
       σ ∈ BHW.petReachableLabelSet (d := d) (n := n) w :=
     (BHW.mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube
       (d := d) (n := n) w σ).2 ⟨Λ, hΛ⟩
   exact
     BHW.petReachableLabelSet_adjacent_connected_of_HW_chamber_curve
       (d := d) hd n w hw σ hσ
   ```

Chosen resolution for the proof-shape seam:

The stale route

```lean
bhw_fixedPoint_activeSliceUnion_connected_of_two_le
-> activePETOrbitAdj_reflTransGen_of_connected_union
-> bhw_fixedPoint_activeSliceGraphConnected_of_two_le
```

is retired.

Reason:

1. connectedness of
   `⋃ a, permLambdaSlice (d := d) n a.1 w`
   controls only the full raw-overlap nerve of the slices;
2. the stricter `PETOrbitChamberChain` edge requires a common Lorentz witness
   in two distinct permuted forward tubes;
3. by `BHW.permutedForwardTube_sector_eq_of_mem`, such a common point forces
   the two permutation labels to be equal, so adjacent nontrivial edges cannot
   exist;
4. the local references verify the BHW analytic continuation on extended
   tubes, not a fixed-`w` forward-tube overlap gallery.

Therefore none of the common-witness fixed-forward-tube chain theorems in the
archived packet below is an active Slot-6 task.  The active Slot-6 task is the
source-backed Hall-Wightman single-valuedness packet displayed earlier.

The following proof transcripts remain in the file only as a record of the
rejected route.  Do not implement them for theorem 2.

Exact proof transcript for the local support items:

1. `one_mem_activePETOrbitLabel_of_forwardTube`:
   use `BHW.one_mem_petReachableLabelSet_of_forwardTube`, then rewrite by
   `mem_petReachableLabelSet_iff_nonempty_permLambdaSlice`.

   ```lean
   refine ⟨1, ?_⟩
   rw [← mem_petReachableLabelSet_iff_nonempty_permLambdaSlice]
   exact BHW.one_mem_petReachableLabelSet_of_forwardTube (d := d) (n := n) hw
   ```

2. `sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube`:
   use the explicit witness `Λ` and rewrite by `mem_permLambdaSlice_iff`.

   ```lean
   refine ⟨σ, ⟨Λ, ?_⟩⟩
   exact (mem_permLambdaSlice_iff (d := d) n σ w Λ).mpr hΛ
   ```

3. `activePETOrbitAdj_implies_petOrbitChamberAdjStep`:
   apply the reverse direction of
   `petOrbitChamberAdjStep_iff_exists_slice_overlap`.

   ```lean
   exact
     (petOrbitChamberAdjStep_iff_exists_slice_overlap
       (d := d) (n := n) w a.1 b.1).2 hab
   ```

Exact proof transcript for the derived endpoint-gallery theorem
`hallWightman_fixedPoint_endpointActiveGallery_of_two_le`:

1. fix `w`, `hw : w ∈ ForwardTube d n`, `σ`, `Λ`, and
   `hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ`;
2. define
   `a0 := one_mem_activePETOrbitLabel_of_forwardTube (d := d) (n := n) w hw`;
3. define
   `aσ := sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
      (d := d) (n := n) w σ Λ hΛ`;
4. apply the fixed-orbit chamber-stratification argument, once documented, in
   the fixed orbit of `w`:
   - the paper-level input is Hall-Wightman extended-tube continuation plus the
     adjacent common real environments recorded in Streater-Wightman Figure
     2-4;
   - Streater-Wightman Theorem 3-6 must not be used as a theorem-2 input,
     because its proof uses local commutativity;
   - the required formal extraction is a finite list of active labels
     `τ 0, ..., τ m : ActivePETOrbitLabel d n w`, with `τ 0 = a0`,
     `τ m = aσ`, and for each `j < m` a common witness `Λj` lying in the two
     neighboring fixed-`w` slices;
5. package that finite data as the active-label gallery in the theorem
   statement.  The later `PETOrbitChamberChain d n w σ` value is built only by
   the mechanical data and packing theorems below.

Documentation-standard proof-local data theorem for the imported packet:

```lean
theorem hallWightman_fixedPoint_adjacentChainData_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        ∃ (m : ℕ) (τ : Fin (m + 1) -> Equiv.Perm (Fin n)),
          τ 0 = 1 ∧
          τ ⟨m, Nat.lt_succ_self m⟩ = σ ∧
          ∀ j : Fin m,
            ∃ (i : Fin n) (hi : i.val + 1 < n) (Λj : ComplexLorentzGroup d),
              τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩ =
                τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩ *
                  Equiv.swap i ⟨i.val + 1, hi⟩ ∧
              complexLorentzAction Λj w ∈
                PermutedForwardTube d n
                  (τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩) ∧
              complexLorentzAction Λj w ∈
                PermutedForwardTube d n
                  (τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩)
```

Obligations hidden inside the endpoint active-gallery theorem, which must be
discharged in the proof doc before a production theorem is attempted:

1. define the active fixed-`w` chamber set as the finite family of nonempty
   slices `permLambdaSlice (d := d) n σ w`;
2. prove that the identity label is active from `hw`, and that the target label
   `σ` is active from the displayed `Λ`;
3. prove the fixed-orbit chamber-stratification input from Hall-Wightman
   extended-tube continuation plus the extra chamber decomposition, not from
   the global set `permForwardOverlapSet`;
4. for every adjacent chamber crossing, produce the adjacent index `i`, the
   equality
   `τ (j + 1) = τ j * Equiv.swap i ⟨i.val + 1, hi⟩`, and a single Lorentz
   transform `Λj` lying in both neighboring permuted forward-tube chambers;
5. use finiteness of `Equiv.Perm (Fin n)` only to package the resulting finite
   chain, not to replace the chamber-stratification theorem by a graph argument
   on an arbitrary raw-overlap nerve.

Detailed proof-local derivation plan for the endpoint gallery:

The object to derive is a **gallery of chambers on one fixed orbit**, not a
connectedness statement about a moving base point. The intended proof doc
should therefore factor the theorem into the following mathematical claims.

#### HW-1. Open fixed-orbit chamber slices

For fixed `w`, each slice

```lean
permLambdaSlice (d := d) n σ w
```

is open in `ComplexLorentzGroup d`, because it is the preimage of
`ForwardTube d n` under the continuous map

```lean
fun Λ => BHW.complexLorentzAction Λ (BHW.permAct (d := d) σ w)
```

Lean-shaped lemma:

```lean
theorem isOpen_permLambdaSlice
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : Fin n -> Fin (d + 1) -> ℂ) :
    IsOpen (permLambdaSlice (d := d) n σ w)
```

This is infrastructure, not the hard theorem.

#### HW-2. Endpoint activity

The identity chamber and target chamber are active:

```lean
have h₀ :
    (permLambdaSlice (d := d) n (1 : Equiv.Perm (Fin n)) w).Nonempty :=
  (one_mem_activePETOrbitLabel_of_forwardTube (d := d) (n := n) w hw).2

have hσ :
    (permLambdaSlice (d := d) n σ w).Nonempty :=
  (sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
    (d := d) (n := n) w σ Λ hΛ).2
```

This only supplies the endpoints; it gives no path and no adjacent gallery.

#### HW-3. Hall-Wightman source audit and derived endpoint-gallery obligation

The original Hall-Wightman paper is present locally as
`references/hall_wightman_invariant_analytic_functions_1957.pdf`
(public Matematisk-fysiske Meddelelser scan).  A first OCR audit of
`/tmp/hall_wightman_1957.txt` gives the following strict source boundary:

1. Theorem I and Lemma I are about Lorentz-invariant holomorphic functions on
   the forward tube. Lemma I extends real Lorentz invariance to the complex
   Lorentz group and gives a single-valued analytic continuation to the
   extended tube.
2. The paper's QFT application says the Wightman functions are determined by
   their values at spacelike separated arguments, and it explicitly says this
   determination result is valid in both local and non-local field theory.
3. The OCR search finds no `permutation`, `transposition`, or adjacent-gallery
   theorem in Hall-Wightman. In particular, the source does not directly state a
   fixed-`w` graph theorem for active labels
   `{τ | (permLambdaSlice (d := d) n τ w).Nonempty}`.
4. OS I Section 4.5 still fixes the dependency order:
   symmetry gives the selected analytic continuation on `S'_n`, the BHW
   theorem enlarges it to `S''_n`, and Jost's theorem is used only afterwards
   for boundary locality.
5. Streater-Wightman Theorem 2-11 has now been audited in the local OCR
   `/tmp/streater_wightman_pct.txt` from
   `references/pct-spin-and-statistics-and-all-that-9781400884230_compress.pdf`.
   It is the non-local BHW analytic-continuation theorem: a family of
   holomorphic tube functions with the transformation law `(2-84)` has a
   single-valued analytic continuation to the extended tube and transforms
   according to `(2-85)` under the proper complex Lorentz group. It does not
   contain a permutation, transposition, or fixed-`w` chamber-gallery theorem.
6. The same Section 2-4 discussion introduces permuted extended tubes only
   after Theorem 2-12. The adjacent-transposition paragraph and Figure 2-4 show
   that `S''_n` and one adjacent permuted extended tube have a common real
   environment. This is a local adjacent real-environment theorem, not a global
   finite active-gallery theorem.
7. Streater-Wightman Figure 2-4 supplies only the local adjacent geometry: for
   one adjacent transposition, the corresponding permuted extended tubes have a
   common real environment. This is a local wall-crossing input, not a global
   gallery theorem by itself.
8. Streater-Wightman Theorem 3-6 is forbidden here because its proof uses local
   commutativity. No step in HW-3 may cite that theorem, even as a shortcut for
   continuing between permuted branches.

Consequently, `hallWightman_fixedPoint_endpointActiveGallery_of_two_le` must
not be advertised as a direct Hall-Wightman paper-extraction theorem. It is an
archived rejected theorem surface, not a theorem-2 dependency. The old route
would have needed a chamber-stratification argument combining:

1. Hall-Wightman single-valued complex-Lorentz continuation on the extended
   tube;
2. the OS I/OS II selected analytic continuation from Euclidean permutation
   symmetry to the permuted forward-tube branches on `S'_n`;
3. the finite chamber decomposition of the fixed complex-Lorentz orbit of one
   forward-tube point `w`;
4. the local adjacent real-environment geometry from Streater-Wightman Figure
   2-4;
5. a proof that the particular identity and target active labels lie in one
   finite adjacent gallery whose edges have actual common fixed-`w` slice
   witnesses.

The old missing chamber-stratification proof would have had to decompose into
the following source-aligned lemmas. These names are retained only to document
why the fixed-`w` route was not made implementation-ready:

1. `bhw_source_singleValuedOn_extendedTube`: source-backed by Hall-Wightman
   Lemma I / Streater-Wightman Theorem 2-11. It should be stated in the local
   extension API as: Lorentz-covariant holomorphic tube data has a
   single-valued continuation to `BHW.ExtendedTube d n`.
2. `sw_adjacentPermutedExtendedTubes_commonRealEnvironment`: source-backed by
   Streater-Wightman Section 2-4 / Figure 2-4. It should assert, for
   `π : Equiv.Perm (Fin n)`, `i : Fin n`, and `hi : i.val + 1 < n`, that
   `BHW.permutedExtendedTubeSector d n π` and the sector for
   `π * Equiv.swap i ⟨i.val + 1, hi⟩` have a common real environment.
3. `fixedOrbit_permutedTubeCover_finiteWallStratification`: new derived
   geometry, not a paper citation. It should pull back the permuted
   forward-tube cover to the fixed complex-Lorentz orbit of
   `w : Fin n -> Fin (d + 1) -> ℂ` and produce a finite wall stratification
   whose codimension-one crossings change labels by adjacent transpositions.
4. `fixedOrbit_endpointGallery_of_sameBHWContinuationSheet`: new derived
   chamber argument. It should prove, from `hw : w ∈ ForwardTube d n`,
   `hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ`, and the
   stratification theorem, that the identity label and the concrete target
   label are connected by a finite adjacent gallery inside the active fixed-`w`
   chamber family.

These four names are archived documentation labels only. They must not be
copied into Lean as placeholder theorem statements.

The rejected derived claim was the following fixed-orbit chamber-refinement
statement, specialized to the theorem-2 endpoints:

1. fix `w ∈ ForwardTube d n`;
2. call a label `τ` active exactly when
   `(permLambdaSlice (d := d) n τ w).Nonempty`;
3. if the target label `σ` is active, witnessed by
   `Λ` with `complexLorentzAction Λ w ∈ PermutedForwardTube d n σ`, then the
   identity active label and the target active label lie in the same finite
   adjacent chamber gallery;
4. every gallery edge has the adjacent-transposition form
   `τ_{j+1} = τ_j * Equiv.swap i ⟨i.val + 1, hi⟩`;
5. every edge carries one actual witness
   `Λj ∈ permLambdaSlice τ_j w ∩ permLambdaSlice τ_{j+1} w`.

This claim is archived because item 5 is impossible for distinct adjacent
labels in the repo's `PermutedForwardTube` geometry. The active theorem-2 route
uses source-backed BHW single-valuedness on `S''_n` instead.

```lean
theorem hallWightman_fixedPoint_endpointActiveGallery_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (hw : w ∈ ForwardTube d n)
    (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ) :
    ∃ (m : ℕ) (α : Fin (m + 1) -> ActivePETOrbitLabel d n w),
      α 0 =
        one_mem_activePETOrbitLabel_of_forwardTube
          (d := d) (n := n) w hw ∧
      α ⟨m, Nat.lt_succ_self m⟩ =
        sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
          (d := d) (n := n) w σ Λ hΛ ∧
      ∀ j : Fin m,
        activePETOrbitAdj d n w
          (α ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩)
          (α ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩)
```

Derived proof meaning:

1. restrict the BHW complex-Lorentz enlargement to the orbit of the fixed
   forward-tube point `w`;
2. form the finite active chamber family
   `{τ : Equiv.Perm (Fin n) | (permLambdaSlice (d := d) n τ w).Nonempty}`;
3. prove the missing chamber-stratification lemma that the identity chamber and
   the concrete target chamber lie in one finite gallery inside that active
   family;
4. refine the gallery so it crosses only neighboring chambers whose labels
   differ by one adjacent transposition;
5. use Streater-Wightman Figure 2-4 only for the local adjacent common-real
   environment, not as a substitute for the fixed-orbit gallery theorem;
6. do not use Streater-Wightman Theorem 3-6 in this proof, since its proof
   assumes local commutativity and would make theorem 2 circular.

Lean-facing proof transcript for the theorem:

1. define the endpoint active labels

   ```lean
   let a0 :=
     one_mem_activePETOrbitLabel_of_forwardTube
       (d := d) (n := n) w hw
   let aσ :=
     sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
       (d := d) (n := n) w σ Λ hΛ
   ```

2. apply the fixed-orbit chamber-stratification theorem, after it has been
   proved from the source-backed Hall-Wightman analytic continuation plus the
   extra finite chamber-refinement argument, to the finite active chamber
   family determined by `w`, with endpoints `a0` and `aσ`;
3. unpack the returned gallery as `m` and
   `α : Fin (m + 1) -> ActivePETOrbitLabel d n w`;
4. the endpoint equalities are exactly the equalities displayed in the theorem
   statement;
5. for each `j : Fin m`, unpack the adjacent wall crossing as
   `i`, `hi`, the label equality, and
   `Λj ∈ permLambdaSlice (α j).1 w ∩ permLambdaSlice (α (j+1)).1 w`;
6. repackage that data as
   `activePETOrbitAdj d n w (α j) (α (j+1))`.

This theorem transcript is archived and rejected for theorem 2: the required
common witness in
`permLambdaSlice (α j).1 w ∩ permLambdaSlice (α (j+1)).1 w` would put one
configuration in two distinct permuted forward tubes.  It may not be revived
as the Slot-6 frontier, and in particular it may not be replaced by:

- `permForwardOverlap_connected_nontrivial`, because that theorem varies the
  base point;
- `BHW.permutedExtendedTube_isPreconnected` or
  `BHW.permutedExtendedTubeSector_adjacent_overlap_nonempty`, because those
  are ambient PET connectedness/overlap statements whose witness point may
  move in configuration space;
- `activePETOrbitAdj_reflTransGen_of_connected_union`, because raw-overlap
  connectedness does not force adjacent-transposition edges;
- `Fin.Perm.adjSwap_induction_right`, because an arbitrary adjacent word need
  not stay inside the active chamber family for this fixed `w`.

#### HW-4. Archived gallery-to-data theorem

In the rejected route, once HW-3 existed, the proof-local data theorem would
have been mechanical. This theorem is not an implementation target:

```lean
theorem hallWightman_fixedPoint_adjacentChainData_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        ∃ (m : ℕ) (τ : Fin (m + 1) -> Equiv.Perm (Fin n)),
          τ 0 = 1 ∧
          τ ⟨m, Nat.lt_succ_self m⟩ = σ ∧
          ∀ j : Fin m,
            ∃ (i : Fin n) (hi : i.val + 1 < n) (Λj : ComplexLorentzGroup d),
              τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩ =
                τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩ *
                  Equiv.swap i ⟨i.val + 1, hi⟩ ∧
              complexLorentzAction Λj w ∈
                PermutedForwardTube d n
                  (τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩) ∧
              complexLorentzAction Λj w ∈
                PermutedForwardTube d n
                  (τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩)
```

Lean-shaped proof:

```lean
  intro w hw σ Λ hΛ
  let a0 :=
    one_mem_activePETOrbitLabel_of_forwardTube
      (d := d) (n := n) w hw
  let aσ :=
    sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
      (d := d) (n := n) w σ Λ hΛ
  obtain ⟨m, α, hstart, hend, hstep⟩ :=
    hallWightman_fixedPoint_endpointActiveGallery_of_two_le
      (d := d) hd n w hw σ Λ hΛ
  refine ⟨m, fun j => (α j).1, ?_, ?_, ?_⟩
  · simpa [a0] using congrArg Subtype.val hstart
  · simpa [aσ] using congrArg Subtype.val hend
  · intro j
    rcases hstep j with ⟨i, hi, hnext, ⟨Λj, hleft, hright⟩⟩
    refine ⟨i, hi, Λj, ?_, ?_, ?_⟩
    · exact hnext
    · exact (mem_permLambdaSlice_iff (d := d) n
        ((α ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩).1) w Λj).mp hleft
    · exact (mem_permLambdaSlice_iff (d := d) n
        ((α ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩).1) w Λj).mp hright
```

This is the first point where the `Λj` witnesses are introduced.  They are
step witnesses, not the endpoint witness `Λ`.

Lean-shaped pseudocode for the theorem packet:

```lean
  intro w hw σ Λ hΛ
  obtain ⟨m, τ, hstart, hend, hstep⟩ :=
    hallWightman_fixedPoint_adjacentChainData_of_two_le
      (d := d) hd n w hw σ Λ hΛ
  exact ⟨m, τ, hstart, hend, hstep⟩
```

Checked internal support already available for implementing this packet:

1. `permLambdaSlice_eq_orbitSet` rewrites every active chamber slice as the
   orbit set of `permAct σ w`.
2. If `a : ActivePETOrbitLabel d n w`, choose `Λa : ComplexLorentzGroup d`
   with `hΛa : Λa ∈ permLambdaSlice (d := d) n a.1 w`.
   Then

   ```lean
   let z := permAct (d := d) a.1 w
   let u := BHW.complexLorentzAction Λa z
   have hu : u ∈ BHW.ForwardTube d n := by
     simpa [z, permLambdaSlice] using hΛa
   have hz : z = BHW.complexLorentzAction Λa⁻¹ u := by
     simp [u, z, BHW.complexLorentzAction_inv]
   ```

3. After supplying the stabilizer-connectedness and orbit-image preconnectedness
   hypotheses used elsewhere in the BHW files, the public theorem
   `BHW.orbitSet_isPreconnected_of_forwardTube_witness`
   gives `IsPreconnected (orbitSet (d := d) (n := n) z)`.
4. Rewriting back along `permLambdaSlice_eq_orbitSet`, every active slice is
   therefore already known locally to be preconnected; the missing content is
   the finite adjacent chamber chain on the fixed orbit, not mere connectedness
   of the raw active union.

This endpoint gallery discussion is archived. It is no longer a theorem-2
dependency packet because the edge relation asks for common permuted
forward-tube membership for distinct labels.

Quarantined proof transcript for the diagnostic corollary
`bhw_fixedPoint_chamberAdjacency_connected_of_two_le`:

This theorem is not on the critical theorem-2 dependency path and is not part
of the implementation gate.  Do not introduce it during theorem-2 work.  The
strict route now goes through
`BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` and
`bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.

1. fix `w`, `σ`, `Λ`, and
   `hΛ : BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ`;
2. obtain `chain := petOrbitChamberChain_of_two_le hd n w hw σ Λ hΛ`;
3. induct on the explicit chain indices `j = 0, ..., m - 1`;
4. each `chain.hstep j` gives one adjacent-swap identity together with the
   common chamber witness `Λj`;
5. turn each step into `PETOrbitChamberAdjStep d n w` directly;
6. append the steps with `Relation.ReflTransGen.tail`;
7. rewrite the endpoints by `chain.hstart` and `chain.hend`.

Exact proof transcript for the packet theorem
`petOrbitChamberChain_of_two_le`:

1. this is the exported finite-chain theorem of the packet;
2. the Lean proof should first call the mechanical data theorem
   `hallWightman_fixedPoint_adjacentChainData_of_two_le`;
3. then pack the returned data into the exact fields of
   `PETOrbitChamberChain`.

Lean-shaped pseudocode for the index-set bridge:

```lean
  exact ⟨w, hw, by
    simpa [BHW.PermutedForwardTube, BHW.permAct, BHW.lorentz_perm_commute] using hΛ⟩
```

Exact constructor transcript for `PETOrbitChamberChain.ofReflTransGen`:

1. induct on the `Relation.ReflTransGen` witness;
2. the reflexive case yields the zero-length chain
   `m := 0`, `τ 0 := 1`;
3. the tail step extends the previously built chain by one permutation label;
4. store the adjacent-swap witness and common chamber witness `Λj` from the
   `PETOrbitChamberAdjStep` hypothesis in the new `hstep` field.

Exact proof transcript for the archived conditional consumer
`petOrbitChamberConnected_of_two_le`:

1. fix `w`, `σ`, `Λ`, and `hΛ : BHW.complexLorentzAction Λ w ∈
   BHW.PermutedForwardTube d n σ`;
2. obtain `chain := petOrbitChamberChain_of_two_le hd n w hw σ Λ hΛ`;
3. convert the chain to `Relation.ReflTransGen` by
   `PETOrbitChamberChain.toReflTransGen`;
4. feed that chain directly into
   `BHW.petReachableLabelSet_adjacent_connected_of_orbitChamberConnected`.

Exact proof transcript for `PETOrbitChamberChain.toReflTransGen`:

1. induct on `j = 0, ..., m - 1`;
2. each `chain.hstep j` gives an adjacent permutation identity and two chamber
   memberships witnessed by the same `Λj`;
3. use
   `BHW.mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube`
   twice to discharge the endpoint memberships in
   `BHW.petReachableLabelAdjStep`;
4. append these adjacent steps with `Relation.ReflTransGen.tail`;
5. rewrite the endpoints by `chain.hstart` and `chain.hend`.

Lean-shaped pseudocode for the consumer theorem:

```lean
  intro w hw σ Λ hΛ
  let chain := petOrbitChamberChain_of_two_le hd n w hw σ Λ hΛ
  exact chain.toReflTransGen
```

This archived common-witness chain is **not** the active Slot-6 target.  It
should not be repaired by swapping in another permutation-flow wrapper.  The
weaker reachable-label `hOrbit` theorem is conditional monodromy
infrastructure, not the strict theorem-2 target.

Full-lane audit boundary beyond the immediate `2 <= d` support stage:

- the monodromy consumers in `PermutedTubeMonodromy.lean` are checked
  conditional BHW infrastructure;
- the active theorem surfaces are the source-backed
  `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`,
  `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry`, and the
  OS specialization `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`;
- the archived fixed-`w` route should not be implemented unless it is first
  redesigned in extended-tube sector language and separately source-audited;
- `bhw_fixedPoint_chamberAdjacency_connected_of_two_le` is explicitly outside
  that gate and may be added later only as a diagnostic corollary with a real
  consumer;
- any genuine `d >= 2` / `d = 1` split must be justified in the source-backed
  Hall-Wightman geometry and the separate one-dimensional complex-edge packet,
  not introduced by wrapper naming.

Hard veto condition:

- this slot may use only non-circular BHW/Hall-Wightman analytic continuation
  input;
- it must **not** depend on
  `blocker_iterated_eow_hExtPerm_d1_nontrivial`.

#### HW-5. Exact Slot-6 production edit packet

When Slot 6 moves to Lean, the production edit should close the
source-backed compatibility theorem using the checked local source support in
`BHWPermutation/SourceExtension.lean`, then expose the source compatibility
theorem and its sector-equality corollary near the selected branch / locality
PET-compat layer.  The archived witness/cover-reaching package should not be
reintroduced as production `sorry` scaffolding without a separate global
Hall-Wightman/Araki source input.  It should not be implemented in the old
common-slice
`PETOrbitChamberChain.lean` style, and it should not replace the source theorem
by an unproved `hOrbit` assumption.

The archived packet below is not permission for a new theorem-level `sorry`:

```lean
/-- Hall-Wightman fixed-orbit endpoint chamber gallery, specialized to the
theorem-2 endpoint pair.

Archived rejected theorem surface.  Do not implement this for theorem 2:
`activePETOrbitAdj` requires a common point in two distinct permuted forward
tubes. -/
theorem hallWightman_fixedPoint_endpointActiveGallery_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ)
    (w : Fin n -> Fin (d + 1) -> ℂ)
    (hw : w ∈ ForwardTube d n)
    (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (hΛ : complexLorentzAction Λ w ∈ PermutedForwardTube d n σ) :
    ∃ (m : ℕ) (α : Fin (m + 1) -> ActivePETOrbitLabel d n w),
      α 0 =
        one_mem_activePETOrbitLabel_of_forwardTube
          (d := d) (n := n) w hw ∧
      α ⟨m, Nat.lt_succ_self m⟩ =
        sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube
          (d := d) (n := n) w σ Λ hΛ ∧
      ∀ j : Fin m,
        activePETOrbitAdj d n w
          (α ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩)
          (α ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩) := by
  sorry
```

The mechanical consumers below are archived with the rejected theorem surface.
They should not be implemented for theorem 2.

```lean
theorem hallWightman_fixedPoint_adjacentChainData_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        ∃ (m : ℕ) (τ : Fin (m + 1) -> Equiv.Perm (Fin n)),
          τ 0 = 1 ∧
          τ ⟨m, Nat.lt_succ_self m⟩ = σ ∧
          ∀ j : Fin m,
            ∃ (i : Fin n) (hi : i.val + 1 < n) (Λj : ComplexLorentzGroup d),
              τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩ =
                τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩ *
                  Equiv.swap i ⟨i.val + 1, hi⟩ ∧
              complexLorentzAction Λj w ∈
                PermutedForwardTube d n
                  (τ ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩) ∧
              complexLorentzAction Λj w ∈
                PermutedForwardTube d n
                  (τ ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩) := by
  intro w hw σ Λ hΛ
  obtain ⟨m, α, hstart, hend, hstep⟩ :=
    hallWightman_fixedPoint_endpointActiveGallery_of_two_le
      (d := d) hd n w hw σ Λ hΛ
  refine ⟨m, fun j => (α j).1, ?_, ?_, ?_⟩
  · simpa [one_mem_activePETOrbitLabel_of_forwardTube] using
      congrArg Subtype.val hstart
  · simpa [sigma_mem_activePETOrbitLabel_of_mem_permutedForwardTube] using
      congrArg Subtype.val hend
  · intro j
    rcases hstep j with ⟨i, hi, hnext, hoverlap⟩
    rcases hoverlap with ⟨Λj, hleft, hright⟩
    refine ⟨i, hi, Λj, hnext, ?_, ?_⟩
    · exact (mem_permLambdaSlice_iff (d := d) n
        ((α ⟨j.val, Nat.lt_succ_of_lt j.is_lt⟩).1) w Λj).mp hleft
    · exact (mem_permLambdaSlice_iff (d := d) n
        ((α ⟨j.val + 1, Nat.succ_lt_succ j.is_lt⟩).1) w Λj).mp hright

theorem petOrbitChamberChain_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        PETOrbitChamberChain d n w σ := by
  intro w hw σ Λ hΛ
  obtain ⟨m, τ, hstart, hend, hstep⟩ :=
    hallWightman_fixedPoint_adjacentChainData_of_two_le
      (d := d) hd n w hw σ Λ hΛ
  exact ⟨m, τ, hstart, hend, hstep⟩

theorem petOrbitChamberConnected_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (n : ℕ) :
    ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
      w ∈ ForwardTube d n ->
      ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
        complexLorentzAction Λ w ∈ PermutedForwardTube d n σ ->
        Relation.ReflTransGen
          (petReachableLabelAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ := by
  intro w hw σ Λ hΛ
  exact
    (petOrbitChamberChain_of_two_le
      (d := d) hd n w hw σ Λ hΛ).toReflTransGen
```

If this archived conditional lane is ever resumed, the verification command for
that later Lean packet will be exactly:

```bash
lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PETOrbitChamberChain.lean
```

Expected result after that later edit, if a separate source audit accepts the
endpoint-gallery theorem as a theorem-level frontier: file success with exactly
one new `declaration uses sorry` warning, attached to
`hallWightman_fixedPoint_endpointActiveGallery_of_two_le`. This is not a
permission to add the `sorry` before the chamber-stratification proof is
documented.

### Conditional Slot 7. `bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData`

If the separate reachable-label `hOrbit` theorem and the selected adjacent
OS/Jost edge packet are ever proved, the checked selected-adjacent PET
branch-independence consumer is:

```lean
theorem bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
        w ∈ BHW.ForwardTube d n ->
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ ->
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (d + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π ->
      z ∈ BHW.permutedExtendedTubeSector d n ρ ->
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k))
```

Proof transcript:

1. use `hEdge` to prove adjacent selected branch equality on every adjacent
   sector overlap;
2. apply
   `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`
   with that adjacent equality and the Slot-6 `hOrbit`;
3. return exactly the displayed conclusion.

Lean-shaped implementation:

```lean
  intro π ρ z hzπ hzρ
  refine
    BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected
      (d := d) (n := n) (bvt_F OS lgc n) ?_ hOrbit π ρ z hzπ hzρ
  intro π i hi z hzπ hzπswap
  simpa [bvt_selectedPETBranch] using
    bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
      (d := d) OS lgc n hEdge π i hi z hzπ hzπswap
```

This theorem reaches all-overlap PET branch independence under the additional
`hOrbit` input.  It is conditional infrastructure, not the strict OS I §4.5
theorem-2 route.

Route correction after the BHW/PET audit: the forbidden object is the
locality-assuming top-level theorem
`BHW.bargmann_hall_wightman_theorem`; the lower-layer BHW monodromy machinery
is checked conditional infrastructure.  Its entry point is:

```lean
theorem bvt_F_extendF_petBranchIndependence_of_selectedAdjacentEdgeData
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (hOrbit :
      ∀ (w : Fin n -> Fin (d + 1) -> ℂ),
        w ∈ BHW.ForwardTube d n ->
        ∀ (σ : Equiv.Perm (Fin n)) (Λ : ComplexLorentzGroup d),
          BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ ->
          Relation.ReflTransGen
            (BHW.petReachableLabelAdjStep (d := d) (n := n) w)
            (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (d + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π ->
      z ∈ BHW.permutedExtendedTubeSector d n ρ ->
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k))
```

This theorem uses `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`
directly.  It does not consume `IsLocallyCommutativeWeak`; the old circular
locality hypothesis is replaced by the OS-II adjacent/Jost input
`SelectedAdjacentPermutationEdgeData` plus the explicit PET orbit-connectivity
obligation `hOrbit`.

Consequently, `bvt_selectedAbsolutePETGluedValue` is no longer an
all-permutation side lane in the conditional monodromy route when used through the checked
`*_of_selectedAdjacentEdgeData` theorems.  It is the glued PET scalar for that
conditional route.  What remains forbidden is constructing or consuming
`SelectedAllPermutationEdgeData` as the theorem-2 route.

### Slot 8. `bvt_F_perm_eq_on_extendedTube_of_two_le`

This is the checked PET-to-ET consequence:

```lean
theorem bvt_F_perm_eq_on_extendedTube_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (τ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (d + 1) -> ℂ),
      z ∈ BHW.ExtendedTube d n ->
      (fun k => z (τ k)) ∈ BHW.ExtendedTube d n ->
      BHW.extendF (bvt_F OS lgc n) (fun k => z (τ k)) =
        BHW.extendF (bvt_F OS lgc n) z
```

Proof:

1. obtain `hPET` from Slot 7;
2. apply
   `BHW.extendF_perm_eq_on_extendedTube_of_petBranchIndependence`.

### Slot 9. `bvt_F_permutation_invariance_on_S'_n_of_two_le`

This is the Lean-facing version of the symmetric continuation on `S'_n`.

```lean
theorem bvt_F_permutation_invariance_on_S'_n_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ {w : Fin n -> Fin (d + 1) -> ℂ}
      (hw : w ∈ BHW.ForwardTube d n)
      {τ : Equiv.Perm (Fin n)} {Γ : ComplexLorentzGroup d},
      BHW.complexLorentzAction Γ (fun k => w (τ k)) ∈
        BHW.ForwardTube d n ->
      bvt_F OS lgc n
        (BHW.complexLorentzAction Γ (fun k => w (τ k))) =
      bvt_F OS lgc n w
```

Proof:

1. obtain `hPET` from Slot 7;
2. apply
   `BHW.F_permutation_invariance_of_petBranchIndependence`
   to `F := bvt_F OS lgc n`.

This is the exact point where the OS route has recovered the symmetric
continuation required before the BHW/Jost boundary step.

### Slot 10. `bvt_F_swapCanonical_pairing_of_spacelike_of_two_le`

This is the theorem-2-specific boundary theorem surface consumed by the checked
transfer theorem in `OSToWightmanBoundaryValuesComparison.lean`.

```lean
theorem bvt_F_swapCanonical_pairing_of_spacelike_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε ->
      (∀ x, f.toFun x ≠ 0 ->
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) ->
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ->
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            (g x)
        =
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            (f x)
```

Mathematical content:

1. use Slot 7 as the single-valued symmetric branch theorem on
   `BHW.PermutedExtendedTube d n`, the Lean representation of `S''_n`;
2. use Slots 8 and 9 as the extended-tube and forward-tube corollaries of that
   BHW enlargement;
3. use the imported Jost boundary theorem
   `bvt_F_jostBoundary_pairing_of_spacelike_of_two_le`
   to conclude the boundary pairing equality on the canonical shell;
4. rewrite that boundary theorem into the displayed canonical-shell pairing
   equality.

This theorem is **not** the dead finite-height route revived.  It is the exact
canonical-pairing consumer that the already-checked boundary-transfer layer
expects.

Lean-ready representation choices for Slot 10:

1. The OS I domain `S'_n` is the finite permuted forward-tube cover
   `BHW.PermutedForwardTube d n π`, quantified over
   `π : Equiv.Perm (Fin n)`.  No new global `SPrime` definition is needed for
   theorem 2; Slot 9 is the forward-tube corollary of the branch-independence
   theorem.
2. The BHW-enlarged domain `S''_n` is exactly
   `BHW.PermutedExtendedTube d n`, with explicit sectors
   `BHW.permutedExtendedTubeSector d n π`.  The relevant checked cover lemmas
   are `BHW.mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube`,
   `BHW.permutedExtendedTube_eq_iUnion_sectors`, and
   `BHW.permutedExtendedTubeSector_subset_permutedExtendedTube`.
3. The symmetric single-valued continuation on `S''_n` is not a separate
   theorem surface in this blueprint.  It is Slot 7,
   `bvt_F_petBranchIndependence_of_two_le`, together with the Slot 8
   extended-tube corollary and the Slot 9 forward-tube corollary.
4. The boundary-value map is not represented by a new ad hoc API.  The
   theorem-2 consumer is the existing
   `bv_local_commutativity_transfer_of_swap_pairing`; its hypotheses are
   supplied by `bvt_boundary_values` and by the canonical-shell pairing theorem
   below.

The only Slot-10 theorem-level analytic frontier that may be introduced is the
Jost boundary theorem with exactly this theorem-2-facing conclusion.  Its proof
is the OS I §4.5 citation to Jost's theorem after the Slot 7-9 symmetric
continuation has been obtained.  It must not use Streater-Wightman Theorem 3-6,
because that theorem assumes local commutativity.

Jost source audit:

1. The local scan
   `references/general-theory-of-quantized-fields.pdf` is image-only, but
   rendering PDF page `49` shows book pages `82` and `83`.
2. The right half, printed page `83`, is titled as the application of the BHW
   theorem to locality. It first records that permutation symmetry can be
   analytically continued from real/permuted points to Wightman functions on
   the permutation-generated BHW domain.
3. The second theorem on printed page `83` is the exact OS I §4.5 citation: if
   `W_{n+1}` has all Wightman-function properties except those derived from
   locality, and is symmetric in all variables, then it satisfies locality.
4. The proof then reduces locality to adjacent transpositions and uses BHW
   analytic continuation plus boundary values. This matches the Slot-10 role:
   consume the symmetric single-valued continuation from Slots 7-9 and output
   the adjacent spacelike boundary equality.

Therefore the Slot-10 theorem is now source-identified. What remains for Lean
is not to rediscover the theorem, but to translate this Jost theorem into the
canonical-shell distributional pairing surface below.

```lean
theorem bvt_F_jostBoundary_pairing_of_spacelike_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε ->
      (∀ x, f.toFun x ≠ 0 ->
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) ->
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ->
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            (g x)
        =
      ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            (f x)
```

Exact proof transcript for
`bvt_F_jostBoundary_pairing_of_spacelike_of_two_le`:

1. fix `n`, `i`, `hi`, `f`, `g`, `ε`, `hε`, `hsp`, `hswap`;
2. set `τ := Equiv.swap i ⟨i.val + 1, hi⟩`;
3. obtain Slot 7 branch independence on `BHW.PermutedExtendedTube d n`;
4. use the Jost theorem cited in OS I §4.5 for the adjacent swap `τ`: the
   hypotheses are exactly the symmetric single-valued analytic continuation on
   `S''_n`, the support condition `hsp`, and the swapped-test equation
   `hswap`;
5. specialize the Jost theorem to the canonical forward-cone shell
   `canonicalForwardConeDirection (d := d) n` and `ε > 0`;
6. rewrite the test on the swapped side using `hswap`, producing the displayed
   integral equality.

Sub-obligations inside the Jost theorem, if the theorem-level frontier is later
opened rather than kept as a single imported theorem:

1. prove the real Jost-neighborhood statement for adjacent spacelike support;
2. identify the two adjacent boundary orderings with the two `S''_n` branches
   supplied by `BHW.PermutedExtendedTube`;
3. prove the canonical-shell membership/limit lemma for
   `canonicalForwardConeDirection`;
4. prove the distributional pairing version for arbitrary
   `SchwartzNPoint d n` tests satisfying `hsp`, using the usual localization
   of distributions rather than a pointwise support shortcut.

Lean-shaped pseudocode for the theorem-2-facing Slot-10 theorem:

```lean
  intro n i hi f g ε hε hsp hswap
  exact
    bvt_F_jostBoundary_pairing_of_spacelike_of_two_le
      (d := d) hd OS lgc n i hi f g ε hε hsp hswap
```

### Slot 11. `bvt_W_swap_pairing_of_spacelike_of_two_le`

This is the final checked consumer step.

Proof pseudocode:

```lean
have hcanonical :=
  bvt_F_swapCanonical_pairing_of_spacelike_of_two_le
    (d := d) hd OS lgc
have hBV := bvt_boundary_values (d := d) OS lgc n
exact
  bv_local_commutativity_transfer_of_swap_pairing
    (d := d) n (bvt_W OS lgc n) (bvt_F OS lgc n) hBV hcanonical
    i ⟨i.val + 1, hi⟩ f g hsupp hswap
```

No theorem below this point is allowed to ask for a general transposition, a
finite-shell equality, or a locality field from a prebuilt
`WightmanFunctions` package.

## 6. Exact dimension-one route

Dimension one is a separate OS-paper lane.  It is not allowed to import the
real-open `2 <= d` OS45 geometry, and it is not allowed to use
`blocker_iterated_eow_hExtPerm_d1_nontrivial`, because that theorem assumes the
target locality statement.

The active `d = 1` route is the direct one-dimensional complex-edge / PET
theorem on the OS I one-gap continuation package.

Forbidden off-route substitutes:

- deriving theorem 2 from a `.choose` permutation-commutation convenience
  theorem;
- introducing a separate `d = 1` complex-Lorentz invariance route unless OS
  itself is shown to use it.

Why this route is forced by the OS paper:

1. OS I's underlying analytic continuation theorem is genuinely one-gap, not a
   many-gap theorem with a hidden global permutation endgame.  See
   `docs/os1_detailed_proof_audit.md`, Section 5.2 ("Why this is only a
   one-gap theorem").
2. OS I §4.5 then uses symmetry + analytic continuation + BHW + Jost to obtain
   locality.  In the current formalization, that means the `d = 1` lane must
   supply its own one-gap complex-edge / Jost analytic input directly, rather
   than trying to inherit locality from the generic permutation-flow package.
3. Therefore the theorem-2 `d = 1` lane is not a discretionary design choice.
   It is the implementation-facing form of the OS I one-gap + locality route.

So the dimension-one closure packet is:

### Slot D1-1. `d1_petBranchIndependence`

```lean
theorem d1_petBranchIndependence
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS)
    (n : ℕ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (1 + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector 1 n π ->
      z ∈ BHW.permutedExtendedTubeSector 1 n ρ ->
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k))
```

This is the dimension-one symmetric-PET single-valuedness theorem required by
OS I §4.5. It is the exact replacement for the circular temptation to use
`blocker_iterated_eow_hExtPerm_d1_nontrivial`, and it is the main `d = 1`
analytic continuation theorem. It is **not** a convenience wrapper.

Exact on-route input package:

```lean
have hAcr := bvt_F_acrOne_package (d := 1) OS lgc n
-- hAcr.1      : holomorphicity on AnalyticContinuationRegion 1 n 1
-- hAcr.2.1    : Euclidean restriction on the zero-diagonal shell
-- hAcr.2.2.1  : global permutation invariance of bvt_F
-- hAcr.2.2.2  : translation invariance of bvt_F
```

Public theorem surface to implement on the strict OS route:

```lean
theorem d1_complexEdge_petBranchIndependence_of_acrOne_package
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS)
    (n : ℕ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (1 + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector 1 n π ->
      z ∈ BHW.permutedExtendedTubeSector 1 n ρ ->
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k))
```

Lean-ready helper packet for this public theorem:

The production packet should use the repository's existing full-configuration
distributional identity API, not a new one-variable test-function API.  The
one-gap nature of OS I is represented by the construction theorem for the data
below: it must build the connected complex edge from `AnalyticContinuationRegion
1 n 1`, but the consumer can reason with ordinary configuration-space sets.

```lean
structure D1AcrOneComplexEdgeData
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS)
    (n : ℕ) (π ρ : Equiv.Perm (Fin n))
    (z : Fin n -> Fin (1 + 1) -> ℂ) where
  U : Set (Fin n -> Fin (1 + 1) -> ℂ)
  V : Set (NPointDomain 1 n)
  H : (Fin n -> Fin (1 + 1) -> ℂ) -> ℂ
  U_open : IsOpen U
  U_connected : IsConnected U
  V_open : IsOpen V
  V_nonempty : V.Nonempty
  wick_mem :
    ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U
  pet_mem : z ∈ U
  H_holo : DifferentiableOn ℂ H U
  H_wick_distribution_zero :
    ∀ φ : SchwartzNPoint 1 n,
      HasCompactSupport (φ : NPointDomain 1 n -> ℂ) ->
      tsupport (φ : NPointDomain 1 n -> ℂ) ⊆ V ->
      ∫ x : NPointDomain 1 n,
          H (fun k => wickRotatePoint (x k)) * φ x = 0
  H_pet_eval :
    H z =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) -
        BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k))
```

The single hard `d = 1` theorem surface is the chart/data construction:

```lean
theorem d1_acrOne_complexEdgeData_of_permutedExtendedTubeSector
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS)
    (n : ℕ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (1 + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector 1 n π ->
      z ∈ BHW.permutedExtendedTubeSector 1 n ρ ->
      D1AcrOneComplexEdgeData OS lgc n π ρ z
```

Mathematical meaning of this surface:

1. reindex by `π⁻¹`, reducing the target pair to `1` versus
   `σ := π⁻¹ * ρ`;
2. use the OS I one-gap `ACR(1)` continuation supplied in Lean by
   `bvt_F_acrOne_package (d := 1) OS lgc n`;
3. choose the one-gap complex edge, with spectator variables frozen, so that
   the target PET point `z` lies in the connected full-configuration image `U`;
4. define `H` as the branch difference on that edge;
5. use `hAcr.2.2.1` to prove the Wick-section distributional zero statement
   `H_wick_distribution_zero`;
6. use `hAcr.2.2.2` only to normalize the one-gap chart, never to change the
   target PET point or weaken the displayed branch equality.

Once that data theorem exists, the PET-point equality is mechanical and uses
the existing full-configuration identity theorem:

```lean
theorem d1_oneGap_complexEdge_zero_on_data
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS)
    (n : ℕ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (1 + 1) -> ℂ)
      (hzπ : z ∈ BHW.permutedExtendedTubeSector 1 n π)
      (hzρ : z ∈ BHW.permutedExtendedTubeSector 1 n ρ),
      let data :=
        d1_acrOne_complexEdgeData_of_permutedExtendedTubeSector
          OS lgc n π ρ z hzπ hzρ
      Set.EqOn data.H (fun _ => 0) data.U := by
  intro π ρ z hzπ hzρ
  let data :=
    d1_acrOne_complexEdgeData_of_permutedExtendedTubeSector
      OS lgc n π ρ z hzπ hzρ
  exact
    eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
      (d := 1) (n := n)
      data.U data.V
      data.U_open data.U_connected data.V_open data.V_nonempty
      data.wick_mem data.H (fun _ => 0) data.H_holo
      (by intro y hy; exact differentiableWithinAt_const (x := y) (c := (0 : ℂ)))
      (by
        intro φ hφ_compact hφ_tsupport
        simpa using data.H_wick_distribution_zero φ hφ_compact hφ_tsupport)

theorem d1_complexEdge_petBranchIndependence_of_acrOne_package
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS)
    (n : ℕ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (1 + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector 1 n π ->
      z ∈ BHW.permutedExtendedTubeSector 1 n ρ ->
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k)) := by
  intro π ρ z hzπ hzρ
  let data :=
    d1_acrOne_complexEdgeData_of_permutedExtendedTubeSector
      OS lgc n π ρ z hzπ hzρ
  have hzero :=
    d1_oneGap_complexEdge_zero_on_data
      OS lgc n π ρ z hzπ hzρ
  have hHz : data.H z = 0 := hzero data.pet_mem
  have hsub :
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) -
        BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k)) = 0 := by
    simpa [data.H_pet_eval] using hHz
  exact sub_eq_zero.mp hsub
```

This slot is the dimension-one analogue of Slots 6-8 in the `2 <= d` lane:
it builds PET single-valuedness directly from the OS I one-gap complex-edge
data theorem, instead of going through orbit-chamber connectedness.  The only
new theorem-level analytic frontier in the initial implementation should be
`d1_acrOne_complexEdgeData_of_permutedExtendedTubeSector`; the later theorems
above are consumers of that data.

### Slot D1-2. `d1_adjacent_sector_compatibility`

```lean
theorem d1_adjacent_sector_compatibility
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS)
    (n : ℕ) :
    ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
      (z : Fin n -> Fin (1 + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector 1 n π ->
      z ∈ BHW.permutedExtendedTubeSector 1 n
        (π * Equiv.swap i ⟨i.val + 1, hi⟩) ->
      BHW.extendF (bvt_F OS lgc n)
        (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k))
```

This is the exact theorem-2-facing local corollary of Slot D1-1. It is not a
separate analytic step.

Lean pseudocode:

```lean
  intro π i hi z hzπ hzπswap
  exact
    d1_petBranchIndependence OS lgc n
      π (π * Equiv.swap i ⟨i.val + 1, hi⟩) z hzπ hzπswap
```

### Slot D1-3. `bvt_F_swapCanonical_pairing_of_spacelike_of_one`

```lean
theorem bvt_F_swapCanonical_pairing_of_spacelike_of_one
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (f g : SchwartzNPoint 1 n) (ε : ℝ), 0 < ε ->
      (∀ x, f.toFun x ≠ 0 ->
        MinkowskiSpace.AreSpacelikeSeparated 1 (x i) (x ⟨i.val + 1, hi⟩)) ->
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ->
      ∫ x : NPointDomain 1 n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := 1) n k μ) * Complex.I) *
            (g x)
        =
      ∫ x : NPointDomain 1 n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := 1) n k μ) * Complex.I) *
            (f x)
```

Proof route:

1. use Slot D1-1 as the one-dimensional symmetric continuation on PET;
2. run the one-gap data theorem
   `d1_acrOne_complexEdgeData_of_permutedExtendedTubeSector` through
   `d1_complexEdge_petBranchIndependence_of_acrOne_package`;
3. rewrite the boundary equality into the canonical pairing equality above.

### Slot D1-4. `bvt_locally_commutative_boundary_route_of_one`

```lean
private theorem bvt_locally_commutative_boundary_route_of_one
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS) :
    IsLocallyCommutativeWeak 1 (bvt_W OS lgc)
```

Proof pseudocode:

```lean
intro n i hi f g hsupp hswap
have hcanonical :=
  bvt_F_swapCanonical_pairing_of_spacelike_of_one OS lgc
have hBV := bvt_boundary_values (d := 1) OS lgc n
exact
  bv_local_commutativity_transfer_of_swap_pairing
    (d := 1) n (bvt_W OS lgc n) (bvt_F OS lgc n) hBV hcanonical
    i ⟨i.val + 1, hi⟩ f g hsupp hswap
```

This is the only acceptable dimension-one theorem-2 closure packet under the
current route discipline.

## 7. Cautionary warning

The only dead route worth remembering is this:

- do **not** try to prove locality by a finite-height canonical-shell theorem
  for `bvt_F`;
- do **not** treat arbitrary transpositions as the primitive locality surface.

Those were not merely unfinished implementation ideas. They were the wrong
theorem surfaces for the OS route.

## 8. Status after this rewrite

This document is intentionally active-route only.  Its readiness claim is now
stagewise rather than global.

### 8.1. Current implementation gate on the current branch

This section is the docs-first handoff gate for the next production Lean pass.
The `2 <= d` route has one active Slot-6/Slot-7 interface.  Its generic BHW
source surface has now been corrected to require the explicit distributional
anchor; implementation should next construct that OS-II anchor and close the
source compatibility theorem.  The direct
hF_perm-only BHW single-valuedness theorem on permuted extended-tube sectors is
archived as unsafe.  The active gate is the distributional
Euclidean/Jost-anchored Hall-Wightman/EOW source theorem, or the OS-specific
specialization that supplies that anchor from the OS-II `bvt_F` construction.
The fixed-`w` forward-tube
endpoint-gallery theorem is archived, not a production frontier.

Exact scope:

1. `Wightman/Reconstruction/WickRotation/OSToWightmanLocalityPETCompat.lean`
   owns Slot 5
   `bvt_F_adjacent_sector_compatibility_of_two_le`.
2. `Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean`
   already owns the selected branch notation and checked local facts
   `bvt_selectedPETBranch`,
   `bvt_selectedPETBranch_holomorphicOn_sector`, and
   `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`.
3. The next theorem-level BHW frontier is the source-backed scalar overlap and
   cover-reaching packet in
   `BHWPermutation/SourceExtension.lean`, culminating in
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`.
4. The OS-specific consumer is
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`, with no
   `IsLocallyCommutativeWeak` hypothesis.  It consumes the
   `BHW.SourceDistributionalAdjacentTubeAnchor` supplied from OS-II selected
   adjacent distributional Jost data.
5. `PETOrbitChamberChain.lean` is archived common-slice infrastructure.
   `PermutedTubeMonodromy.lean` is conditional infrastructure through the
   checked lower-layer consumer
   `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`.

Exact verification boundary for that stage:

1. `lake env lean
   OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtension.lean`
2. `lake env lean
   OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityPETCompat.lean`
3. `lake env lean
   OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean`
4. `lake env lean
   OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocality.lean`
5. `lake env lean
   OSReconstruction/Wightman/Reconstruction/WickRotation.lean`

The exact Lean verification boundary above is recorded for later.  It is not a
signal to widen theorem-2 implementation before the OS-specific
distributional Jost anchor has been constructed and the Euclidean-anchored
source theorem has been proved or explicitly approved as a source import under
`AGENT.md`.

### 8.2. Later documented stages on the same theorem-2 route

The rest of the theorem-2 route is also fixed here, but it is not part of the
immediate implementation gate above.

1. The checked OS45 geometry / Euclidean-edge layer is recorded in Section 3.
2. The `2 <= d` route is frozen as Slots 1-11.
3. Slot 6 is the source-backed Hall-Wightman theorem
   `hallWightman_source_permutedBranch_compatibility_of_distributionalAnchor`
   plus the assembly/equality corollaries
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` and
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry`.
4. Slot 7 is the OS specialization
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`, fed by the
   OS-II selected adjacent distributional Jost anchor through
   `BHW.SourceDistributionalAdjacentTubeAnchor`.
5. The `d = 1` route is frozen as Slots D1-1 through D1-4.
6. The `d = 1` external analytic input is the one-gap data theorem
   `d1_acrOne_complexEdgeData_of_permutedExtendedTubeSector`; the zero-on-data,
   PET-evaluation, and adjacent-sector compatibility theorems are mechanical
   consumers of that package plus the existing connected identity-theorem
   infrastructure.
7. The exact boundary-transfer consumer is
   `bv_local_commutativity_transfer_of_swap_pairing`.
8. The archived BHW monodromy consumer
   `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`
   must not be used for theorem 2 unless its geometry input is restated and
   source-audited in extended-tube terms.

If later work needs a theorem not named in Sections 4-6, that is a sign that
the route has drifted and this blueprint should be revised before more
production Lean is written.
