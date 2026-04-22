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
That sibling note owns the external BHW permutation-geometry obligations.  The
present note owns the theorem-2 consumer chain from the OS45 local edge packet
to the final `bvt_W` locality theorem.

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

This wrapper is theorem-2-facing only; it must not introduce any new geometry
or any all-permutation edge-data structure.

### Slot 6. `petOrbitChamberConnected_of_two_le`

This is the exact external BHW permutation-geometry input needed next.  It is
the `hOrbit` hypothesis of
`BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`.

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

Mathematical role:

- this is the Lean-facing BHW monodromy geometry theorem for the `d >= 2`
  branch;
- it packages the statement that the complex-Lorentz orbit of a forward-tube
  point meets a Cayley-connected set of permuted forward-tube chambers;
- it is the correct place to consume the external BHW geometry obligation from
  `bhw_permutation_blueprint.md`.

Exact proof transcript:

1. use `JostWitnessGeneralSigma.jostWitness_exists` to get the nonempty seed
   packet for each nontrivial permutation chamber;
2. use `blocker_isConnected_permSeedSet_nontrivial` as the only deferred
   geometric input on the `d >= 2` branch;
3. transport that connectedness through
   `isConnected_permSeedSet_iff_permForwardOverlapSet`;
4. convert the resulting orbit/chamber connectedness into the displayed
   reachable-label chain by the checked adapters in
   `PermutedTubeMonodromy.lean`.

Hard veto condition:

- this slot may depend on
  `blocker_isConnected_permSeedSet_nontrivial`;
- it must **not** depend on
  `blocker_iterated_eow_hExtPerm_d1_nontrivial`.

### Slot 7. `bvt_F_petBranchIndependence_of_two_le`

Once Slots 4-6 exist, the next theorem is the checked monodromy consumer:

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

1. let `hEdge := bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le hd OS lgc n`;
2. build `hAdj` by Slot 5 from `hEdge`;
3. build `hOrbit` by Slot 6;
4. apply
   `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`
   to `F := bvt_F OS lgc n`.

This theorem is the first place where the theorem-2 route reaches the
all-overlap PET single-valuedness required by OS I §4.5.

At this point the route must still stay on the generic checked monodromy
theorems above.  It must **not** try to replace Slot 7 by constructing
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

1. use Slot 9 as the symmetric continuation on the permuted forward-tube
   union `S'_n`;
2. use the BHW enlargement theorem to pass to the complex-Lorentz saturation
   `S''_n`;
3. use the cited Jost boundary theorem to conclude locality of the boundary
   distributions;
4. rewrite the resulting boundary equality into the displayed canonical-shell
   pairing equality.

This theorem is **not** the dead finite-height route revived.  It is the exact
canonical-pairing consumer that the already-checked boundary-transfer layer
expects.

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

The dimension-one closure packet is:

### Slot D1-1. `d1_adjacent_sector_compatibility`

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

This is the direct one-dimensional complex-edge / symmetric-PET theorem.  It
must be proved from the one-dimensional boundary theorem on the complex edge,
not by appealing to any theorem that already assumes
`IsLocallyCommutativeWeak 1 (bvt_W OS lgc)`.

### Slot D1-2. `d1_petBranchIndependence`

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

This is the dimension-one symmetric-PET single-valuedness statement.  It is the
exact replacement for the circular temptation to use
`blocker_iterated_eow_hExtPerm_d1_nontrivial`.

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

1. use Slot D1-2 as the one-dimensional symmetric continuation on PET;
2. run the cited one-dimensional Jost boundary theorem;
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

This document is now intentionally active-route only and is meant to be
implementation-ready.

- The checked OS45 geometry / Euclidean-edge layer is recorded in Section 3.
- The `2 <= d` route is frozen as Slots 1-11.
- The `d = 1` route is frozen as Slots D1-1 through D1-4.
- The exact boundary-transfer consumer is now named:
  `bv_local_commutativity_transfer_of_swap_pairing`.
- The exact BHW monodromy consumer is now named:
  `BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`.

If later work needs a theorem not named in Sections 4-6, that is a sign that
the route has drifted and this blueprint should be revised before more
production Lean is written.
