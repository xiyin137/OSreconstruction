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

## 5. Checked downstream chain after Slot 4

Once Slot 4 is proved, the rest of the `2 <= d` route should consume checked
theorems, not create new local geometry.

1. `bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`
   gives equality of the selected `extendF` branches on the whole adjacent
   ET/swap-ET overlap.
2. `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`
   gives adjacent compatibility of the selected PET branches.
3. The existing PET gluing / monodromy package then promotes adjacent
   compatibility to the symmetric continuation on the relevant PET/BHW domain.
4. The external BHW/Jost boundary-value route converts that symmetric
   continuation into locality of the boundary distributions.
5. The existing boundary-transfer layer closes
   `bvt_W_swap_pairing_of_spacelike`.

No new theorem slot below `bvt_W_swap_pairing_of_spacelike` should ask for a
general transposition, a finite-shell equality, or a prepackaged locality field
from `os_to_wightman_full`.

## 6. Dimension-one route

Dimension one is a separate closure theorem and should stay separate.

```lean
private theorem bvt_locally_commutative_boundary_route_of_one
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS) :
    IsLocallyCommutativeWeak 1 (bvt_W OS lgc)
```

This route must use the documented D1-C complex-edge / symmetric-PET argument.
It must not delay the `2 <= d` supplier chain, and it must not import the
real-open `2 <= d` OS45 geometry as though it were available in dimension one.

## 7. Cautionary warning

The only dead route worth remembering is this:

- do **not** try to prove locality by a finite-height canonical-shell theorem
  for `bvt_F`;
- do **not** treat arbitrary transpositions as the primitive locality surface.

Those were not merely unfinished implementation ideas. They were the wrong
theorem surfaces for the OS route.

## 8. Status after this rewrite

This document is now intentionally active-route only.

- The checked OS45 geometry / Euclidean-edge layer is recorded in Section 3.
- The first unproved theorem on the active route is
  `os45_adjacent_singleChart_commonBoundaryValue`.
- The required downstream consumer shape is fixed by
  `SelectedAdjacentPermutationEdgeData`.

If later work needs a theorem not named in Sections 4-6, that is a sign that
the route has drifted and this blueprint should be revised before more
production Lean is written.
