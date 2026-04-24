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
   is now the direct OS I §4.5 / Hall-Wightman packet on the permuted extended
   tube: the source branch-law theorem
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`,
   the proved source-extension assembly theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry`, the derived
   sector equality theorem
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry`, and the
   OS specialization
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`, feeding the
   public Slot-7 branch-independence theorem
   `bvt_F_petBranchIndependence_of_two_le`.  The earlier fixed-`w`
   forward-tube chamber-chain packet is rejected for theorem 2: its proposed
   edges require one point to lie in two distinct permuted forward tubes, while
   the repository already proves
   `BHW.permutedForwardTube_sector_eq_of_mem` and
   `BHW.forwardTube_inter_permutedForwardTube_eq_empty_of_ne_one`.
   Any remaining fixed-fiber graph theorem is background geometry only unless
   it is restated entirely in extended-tube sector language and source-checked
   against OS I §4.5.
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

This matches the corrected primitive locality surface
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

1. **OS-internal Euclidean symmetry layer.**
   Use `E3_symmetric` on ordered positive-time zero-diagonal tests and the
   already-checked Euclidean/Wick identification to prove that the adjacent
   Wick branch difference has zero Euclidean edge distribution on the chosen
   ordered real patch.

2. **Local common-boundary / EOW layer.**
   Near a real adjacent Jost edge point, realize the same adjacent
   branch-difference object on a common local chart and use the already-proved
   common-boundary / edge-of-the-wedge theorem to continue it from the
   Euclidean edge to the real Jost edge.

3. **Selected adjacent edge-data packaging.**
   Package the resulting compact-test equality on one real-open edge slice
   together with overlap connectedness as
   `SelectedAdjacentPermutationEdgeData`.

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

- `SelectedAdjacentPermutationEdgeData`
- `bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`
- `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`

These are downstream consumers. The OS45 supplier must target their exact input
shape rather than inventing a parallel interface.

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

These files are checked algebra.  They are **not** a license to skip the
missing BHW/Jost geometry input.  In particular:

1. `PermutedTubeGluing.lean` assumes all-overlap compatibility on PET; it does
   not create that compatibility from adjacent data.
2. `PermutedTubeMonodromy.lean` reduces adjacent compatibility to all-overlap
   compatibility **once** the fixed-fiber / reachable-label geometry is
   supplied.
3. theorem 2 must stay on this monodromy file, not on the generic
   `PermutationFlow.iterated_eow_permutation_extension` consumer, because the
   latter mixes in the deferred dimension-one blocker
   `blocker_iterated_eow_hExtPerm_d1_nontrivial`.

## 4. Exact remaining theorem slots for `2 <= d`

The active `2 <= d` route is the following exact chain.

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
      AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
        (Equiv.swap i ⟨i.val + 1, hi⟩) V
```

Mathematical content:

- choose `V` and `rho` from `os45_adjacent_localEOWGeometry`;
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
- define the corresponding adjacent branch-difference object on the Wick /
  Euclidean side and prove, via
  `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`, that its Euclidean
  edge distribution is zero on the ordered real patch;
- use local common-boundary / EOW to show that the Wick-side and real-side
  branch differences are traces of one common holomorphic object on `U`;
- conclude from the zero Euclidean edge distribution that this common
  branch-difference object vanishes, hence the real-edge adjacent difference
  vanishes on the selected edge slice;
- package that vanishing result as an `AdjacentOSEOWDifferenceEnvelope`.

This theorem is where the actual OS I §4.5 local common-boundary argument lives.
It is not a replacement for the paper route; it is the local chart-level
formalization of the OS branch-difference step.

Checked support already available for Slot 1 after checkpoint `1ad959e`:

- `os45PulledRealBranch`
- `os45PulledRealBranch_holomorphicOn`
- `os45PulledRealBranch_apply_realBranch`
- `os45QuarterTurnConfig_reindexed_realBranch_eq`
- `os45PulledRealBranch_apply_reindexed_commonPoint`
- `os45PulledRealBranch_sub_eq_adjacentOS45RealEdgeDifference`

These theorems live in
`OSToWightmanLocalityOS45BranchPullback.lean`.  Their role is precise:
they provide a non-tautological common-chart representation of the
negative-side real branch difference.  They do **not** close Slot 1 by
themselves.

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

Why this still does **not** finish Slot 1:

- at a Wick point one has
  `P_id(Q(z)) = bvt_F z` only when the chart point lies in the forward tube;
- similarly
  `P_swap(Q(z)) = bvt_F (permAct τ z)` only when the permuted Wick point also
  lies in the forward tube;
- the simultaneous forward-tube condition is a thin equal-time constraint, not
  the open agreement set required by a naive identity-theorem argument.

Therefore Slot 1 must still consume the full OS-paper downstream packet:

1. adjacent PET-sector compatibility (Slot 5),
2. BHW orbit/chamber connectivity (Slot 6),
3. PET branch independence / symmetric continuation (Slot 7),
4. only then the Jost boundary step and the real-edge packaging.

The branch-pullback support is genuine progress, but only as negative-side
chart infrastructure for that later common-boundary packaging.

Active decomposition of Slot 1:

1. build the local connected domain `U` on which the adjacent Wick-side and
   real-side branch differences are both represented after the common-chart
   placement;
2. prove zero Euclidean edge distribution for the Wick-side adjacent branch
   difference using `os45_adjacent_euclideanEdge_pairing_eq_on_timeSector`;
3. run the local common-boundary / EOW step to identify the Wick-side and
   real-side branch differences as traces of one holomorphic object on `U`;
4. use the zero Euclidean edge distribution to conclude the common object
   vanishes and hence the real-edge adjacent difference vanishes;
5. package the resulting real-edge vanishing as
   `AdjacentOSEOWDifferenceEnvelope`.

With that choice:

- the positive-side envelope trace is the honest Wick-side adjacent branch
  difference, whose Euclidean edge distribution vanishes by E3;
- the negative-side envelope trace is the honest adjacent real-edge
  `extendF` difference;
- no tautological selected-branch cancellation appears anywhere in the active
  route;
- no local theorem slot is allowed to bypass the OS sequence
  symmetry -> continuation -> BHW -> Jost -> boundary locality.

The old "common-chart Wick difference" route is dead and should not be revived
in production code except as a cautionary note.

Implementation-order note:

- the theorem surface remains Slot 1;
- the next production theorem to implement is nevertheless Slot 5, because the
  checked branch-pullback support above does not close Slot 1 on its own, while
  Slot 5 is an already-determined theorem-2-facing wrapper on the strict OS
  route.

Immediate branch-stage clarification:

- the current branch-stage implementation target is the `2 <= d` direct BHW
  single-valuedness packet;
- that packet consists of:
  1. Slot 5 in
     `Wightman/Reconstruction/WickRotation/OSToWightmanLocalityPETCompat.lean`,
  2. the selected branch facts in
     `Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean`,
  3. the direct BHW theorem
     `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`;
- within that stage, the only allowed new theorem-level frontier is the
  imported/source-backed direct BHW theorem above;
- no `d = 1` implementation, Slot-10 imported boundary theorem, theorem-4 work,
  or generic permutation-flow endgame belongs to this stage.

### Slot 2. `bvt_F_adjacent_edgeWitness_from_OS_ACR_of_two_le`

Once Slot 1 exists, the compact-test edge theorem is already checked:
`bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`.

So the next theorem is a packaging theorem:

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

This is a short wrapper theorem. It should be proved only from the already
checked connectedness/adjacent-overlap infrastructure in
`ComplexLieGroups/Connectedness`, not by reopening locality arguments.

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

### Slot 6. `petOrbitChamberConnected_of_two_le`

This section is kept to explain a rejected interface.  It is no longer the
active theorem-2 Slot 6.

The proposed `petOrbitChamberConnected_of_two_le` route was attractive because
it would have fed the checked monodromy theorem
`BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`.
However, the concrete finite-chain packet documented below strengthened the
edge relation to a common fixed-`w` **permuted forward-tube** slice.  That edge
cannot exist for distinct adjacent labels.

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

Correct replacement:

Slot 6 should be split into a generic source-backed BHW theorem and an
OS-specific specialization.  The generic analytic input must not mention OS,
Wightman distributions, locality, or boundary values.

The one remaining source frontier is the Hall-Wightman branch-law theorem:

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

The theorem-2-facing source extension theorem is now the proved PET-algebra
assembly from that branch law:

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
        F (fun k => z (σ k)) = F z) :
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
        F (fun k => z (σ k)) = F z) :
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
      (d := d) hd n F hF_holo hF_lorentz hF_perm
  exact (hFpet_branch π z hzπ).symm.trans (hFpet_branch ρ z hzρ)
```

Together these two generic theorems are the direct local Lean form of the OS I
§4.5 use of Hall-Wightman/BHW: a real-Lorentz-invariant symmetric holomorphic
datum on the permuted forward-tube family `S'_n` has a single-valued symmetric
`L_+(ℂ)`-invariant continuation on the complex-Lorentz saturation `S''_n`.

Implementation discipline: the branch-law theorem is the only theorem-level
analytic frontier in `SourceExtension.lean`; the source extension theorem and
the branch-equality theorem are mechanical consumers of it.  None of these
theorems may be introduced as an `axiom` without the user's explicit approval.
All statements are intentionally pure SCV/BHW and contain no OS or QFT-specific
objects.

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

Lean-shaped specialization proof:

```lean
  intro π ρ z hzπ hzρ
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
      π ρ z hzπ hzρ
```

In the current Lean representation, `S''_n` is covered by the sectors
`BHW.permutedExtendedTubeSector d n π`; the checked cover facts are
`BHW.mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube`,
`BHW.permutedExtendedTube_eq_iUnion_sectors`, and
`BHW.permutedExtendedTubeSector_subset_permutedExtendedTube`.

Exact proof transcript for the replacement:

1. prove or import
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`
   as the pure SCV/BHW source theorem;
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
6. the hard Hall-Wightman source step is exactly the assertion that these
   branches are restrictions of one single-valued holomorphic function `Fpet`
   on `BHW.PermutedExtendedTube d n`, with the displayed branch law;

   This is a genuine Hall-Wightman compatibility step, not a shortcut from the
   raw formula `hF_perm`.  If `z` lies in two PET sectors, the two branch values
   are obtained by choosing complex-Lorentz representatives of
   `(fun k => z (π k))` and `(fun k => z (ρ k))` in the base extended tube.
   The point produced after permuting one representative and transporting it by
   the other complex Lorentz transform need not lie in `BHW.ForwardTube d n`.
   Therefore the ordinary forward-tube invariance of `F`, even combined with
   pointwise permutation symmetry, does not by itself prove all-sector branch
   equality.  The source input must be Hall-Wightman's one-function
   single-valued continuation for the symmetric permuted-tube datum on `S'_n`,
   enlarged to `S''_n`.

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
   have hHW :
       ∃ Fpet,
         DifferentiableOn ℂ Fpet (BHW.PermutedExtendedTube d n) ∧
         (∀ π z, z ∈ BHW.permutedExtendedTubeSector d n π ->
           Fpet z = G π z) := by
     -- this is exactly the remaining source theorem content
     sorry
   ```

   The final Lean theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` now consumes
   this source branch law and proves the forward-tube agreement,
   complex-Lorentz invariance, and permutation invariance outputs.
7. derive
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` from that
   branch law by the two-line `Fpet` comparison above;
8. supply `hF_holo` from `bvt_F_holomorphic`;
9. supply `hF_lorentz` from
   `bvt_F_restrictedLorentzInvariant_forwardTube`;
10. supply `hF_perm` from `bvt_F_perm`;
11. specialize the generic equality theorem to any common sector point `z` and labels
   `π`, `ρ`;
12. rewrite `bvt_selectedPETBranch` to the displayed `BHW.extendF` expression
   used by Slot 7.

The local helper `BHW.gluedPETValue` is downstream packaging only.  Its theorem
`BHW.gluedPETValue_holomorphicOn` assumes all-sector compatibility
`hcompat`; it does not prove the Hall-Wightman single-valuedness theorem.
After the source theorem has supplied the branch law, `gluedPETValue` may be
used to name the resulting `Fpet`, but it is not the analytic input.

Lean implementation packet for the next pass:

1. Put the pure source theorem in a new small file:
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtension.lean`.
   Do not place it in `BHWPermutation/PermutationFlow.lean`; that file contains
   circular theorem surfaces used only as historical infrastructure.
2. The planned imports for the new file are:

```lean
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvarianceCore
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeConnected
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTubeGluing
import OSReconstruction.ComplexLieGroups.JostPoints
```

   If Lean shows that `JostPoints` already exports one of these dependencies,
   the implementation may minimize imports, but it must not import
   `BHWPermutation.PermutationFlow` to get the source theorem.
3. Add the new file to the aggregate import
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation.lean` only
   after the file has an exact successful
   `lake env lean
   OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/SourceExtension.lean`
   check.
4. The exact later verification sequence for this packet is:

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

The only allowed theorem-level frontier in this new file is
`BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`.
The theorem `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` is the
proved assembly theorem from that branch law, and
`BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` must remain its
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
3. Therefore the active generic Lean frontier is the collapsed one-function
   specialization of the source branch law to the branch family
   `F_π z = F (fun k => z (π k))`.  The permutation hypothesis
   `hF_perm` identifies this as the symmetric `S'_n` datum; the BHW theorem
   supplies the single-valuedness on `S''_n`.
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
8. The small theorem-2-facing consumer after Slot 6 is now the public Slot-7
   wrapper `bvt_F_petBranchIndependence_of_two_le`, not
   `petOrbitChamberConnected_of_two_le`.

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
   `petOrbitChamberChain_of_two_le`, and
   `petOrbitChamberConnected_of_two_le` are not active theorem-2 surfaces.
3. The reason is not merely missing documentation: the common-slice edge
   required by this packet would put one point in two distinct permuted forward
   tubes, contradicting `BHW.permutedForwardTube_sector_eq_of_mem`.
4. These names may remain in experimental geometry files, but theorem 2 should
   move through `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.

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

The inventory below is therefore a target inventory, not a statement that every
displayed theorem is already exported by the current Lean files:

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
permuted-forward-tube disjointness.  The active Slot-6 docs should instead be
read as the direct BHW single-valuedness theorem on permuted extended-tube
sectors.

The checked reduction chain in `PermutedTubeMonodromy.lean` is:

```lean
theorem petReachableLabelSet_adjacent_connected_of_orbitChamberConnected
theorem petSectorFiber_adjacent_connected_of_reachableLabelConnected
theorem extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected
```

The checked reduction chain remains useful background infrastructure, but
Slot 6 should not be treated as an `hOrbit` proof obligation for theorem 2.

What the rejected theorem would have had to accomplish mathematically was:
for fixed `w` and `Λ · w`, build a finite chamber chain

```lean
1 = τ₀, τ₁, ..., τₘ = σ
```

such that each successive chamber overlap has a Lorentz witness `Λj` acting on
the same fixed point `w`.  The endpoint witness `Λ` only proves that `σ` is an
active label; it is not assumed to lie in every intermediate overlap.  Each
overlap gives one `BHW.petReachableLabelAdjStep`, and the whole finite chain is
then packaged as `Relation.ReflTransGen`.

So the exact theorem order for Slot 6 is:

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

Therefore none of the fixed-forward-tube chain theorems in the archived packet
below is an active Slot-6 task.  The active Slot-6 task is the direct BHW
single-valuedness theorem on permuted extended-tube sectors displayed above.

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
not be advertised as a direct Hall-Wightman paper-extraction theorem. It is the
candidate Lean-facing **derived** theorem needed by Slot 6. To make it
mathematically ready, the proof docs still have to supply the missing
chamber-stratification argument combining:

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

The missing chamber-stratification proof should be decomposed into the
following source-aligned lemmas before Lean implementation:

Lean-shaped lemma inventory for the next documentation pass:

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

These four names are documentation labels only until the exact local theorem
statements are written out. They must not be copied into Lean as placeholder
theorem statements.

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
uses extended-tube sectors and direct BHW single-valuedness instead.

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

#### HW-4. Gallery-to-data theorem

Once HW-3 exists, the proof-local data theorem is mechanical:

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

Exact proof transcript for the theorem-2-facing consumer
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

This archived BHW chamber-connectedness target is **not** the active Slot-6
target.  It should not be repaired by swapping in another permutation-flow
wrapper; theorem 2 now uses the direct BHW single-valuedness theorem on
permuted extended-tube sectors.

Full-lane audit boundary beyond the immediate `2 <= d` support stage:

- the monodromy consumers in `PermutedTubeMonodromy.lean` are background
  infrastructure, not the active theorem-2 route;
- the active theorem surface is
  `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`;
- the archived fixed-`w` route should not be implemented unless it is first
  redesigned in extended-tube sector language and separately source-audited;
- `bhw_fixedPoint_chamberAdjacency_connected_of_two_le` is explicitly outside
  that gate and may be added later only as a diagnostic corollary with a real
  consumer;
- any genuine `d >= 2` / `d = 1` split must be justified in the direct BHW
  theorem and the separate one-dimensional complex-edge packet, not introduced
  by wrapper naming.

Hard veto condition:

- this slot may use only non-circular BHW/Hall-Wightman analytic continuation
  input;
- it must **not** depend on
  `blocker_iterated_eow_hExtPerm_d1_nontrivial`.

#### HW-5. Exact Slot-6 production edit packet

When Slot 6 moves to Lean, the production edit should introduce or expose the
direct theorem
`bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le` near the selected
branch / locality PET-compat layer, not in
`PETOrbitChamberChain.lean`.

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

The verification command for the later Lean packet will be exactly:

```bash
lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PETOrbitChamberChain.lean
```

Expected result after that later edit, if the docs accept the endpoint-gallery
theorem as a theorem-level frontier: file success with exactly one new
`declaration uses sorry` warning, attached to
`hallWightman_fixedPoint_endpointActiveGallery_of_two_le`. This is not a
permission to add the `sorry` before the chamber-stratification proof is
documented.

### Slot 7. `bvt_F_petBranchIndependence_of_two_le`

Once the direct Slot-6 BHW single-valuedness theorem exists, the next theorem
is the PET branch-independence theorem:

```lean
theorem bvt_F_petBranchIndependence_of_two_le
    [NeZero d]
    (hd : 2 <= d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n -> Fin (d + 1) -> ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π ->
      z ∈ BHW.permutedExtendedTubeSector d n ρ ->
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k)) =
        BHW.extendF (bvt_F OS lgc n) (fun k => z (ρ k))
```

Proof transcript:

1. formulate the BHW theorem exactly as OS I §4.5 uses it: a symmetric
   holomorphic continuation on `S'_n`, represented by the selected branches on
   `BHW.PermutedForwardTube d n π`, extends single-valuedly to the
   complex-Lorentz saturation `S''_n`, represented by
   `BHW.PermutedExtendedTube d n`;
2. use the checked Slot-5 adjacent branch agreement only to identify the
   selected branches on the local overlaps needed to form the `S'_n`
   symmetric analytic datum;
3. apply the source-backed BHW theorem to obtain equality of selected branches
   on every common sector point of `BHW.PermutedExtendedTube d n`;
4. return exactly the displayed conclusion of
   `bvt_F_petBranchIndependence_of_two_le`.

Lean-shaped implementation:

```lean
  intro π ρ z hzπ hzρ
  simpa [bvt_selectedPETBranch] using
    bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le
      (d := d) hd OS lgc n π ρ z hzπ hzρ
```

This theorem is the first place where the theorem-2 route reaches the
all-overlap PET single-valuedness required by OS I §4.5.

At this point the route must stay within the source-audited direct BHW
transcript above. It must **not** try to replace Slot 7 by constructing
`SelectedAllPermutationEdgeData` or by switching to
`bvt_selectedAbsolutePETGluedValue`; those surfaces belong to the
all-permutation helper lane, not to the strict theorem-2 consumer packet.

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
The `2 <= d` route now has one active Slot-6/Slot-7 interface: the direct
source-backed BHW single-valuedness theorem on permuted extended-tube sectors.
The fixed-`w` forward-tube endpoint-gallery theorem is archived, not a
production frontier.

Exact scope:

1. `Wightman/Reconstruction/WickRotation/OSToWightmanLocalityPETCompat.lean`
   owns Slot 5
   `bvt_F_adjacent_sector_compatibility_of_two_le`.
2. `Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean`
   already owns the selected branch notation and checked local facts
   `bvt_selectedPETBranch`,
   `bvt_selectedPETBranch_holomorphicOn_sector`, and
   `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`.
3. The next theorem-level analytic frontier is the pure BHW/SCV branch-law
   theorem
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`;
   the source extension theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry` is now proved
   from that branch law, and the sector equality theorem
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` is its
   mechanical corollary.
4. The OS-specific specialization is
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`, with no
   `IsLocallyCommutativeWeak` hypothesis; it consumes
   `bvt_F_holomorphic`,
   `bvt_F_restrictedLorentzInvariant_forwardTube`, and `bvt_F_perm`.
5. The public consumer is
   `bvt_F_petBranchIndependence_of_two_le`, whose proof is the short wrapper
   around the direct BHW theorem.
6. `PETOrbitChamberChain.lean` and `PermutedTubeMonodromy.lean` are background
   infrastructure for the archived graph route.  They are not the active
   theorem-2 implementation surface.

Exact verification boundary for that stage:

1. `lake env lean
   OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocalityPETCompat.lean`
2. `lake env lean
   OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSelectedWitness.lean`
3. `lake env lean
   OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanLocality.lean`
4. `lake env lean
   OSReconstruction/Wightman/Reconstruction/WickRotation.lean`

The exact Lean verification boundary above is recorded for later.  It is not a
signal to start implementation before the direct BHW theorem statement has
been audited against OS I §4.5 and the Hall-Wightman source.

### 8.2. Later documented stages on the same theorem-2 route

The rest of the theorem-2 route is also fixed here, but it is not part of the
immediate implementation gate above.

1. The checked OS45 geometry / Euclidean-edge layer is recorded in Section 3.
2. The `2 <= d` route is frozen as Slots 1-11.
3. Slot 6 is the generic direct BHW source branch-law theorem
   `BHW.hallWightman_permutedExtendedTube_branchLaw_of_forwardTube_symmetry`,
   followed by the proved assembly theorem
   `BHW.permutedExtendedTube_extension_of_forwardTube_symmetry`, the sector
   equality theorem
   `BHW.permutedExtendedTube_singleValued_of_forwardTube_symmetry` and the
   OS-specific specialization
   `bvt_F_bhwSingleValuedOn_permutedExtendedTube_of_two_le`.
4. Slot 7 is the public PET branch-independence wrapper
   `bvt_F_petBranchIndependence_of_two_le`.
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
