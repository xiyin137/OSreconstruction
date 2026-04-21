# Theorem 2 Locality Blueprint

Purpose: this note is the theorem-specific implementation blueprint for the
theorem-2 `E -> R` locality frontier.  The current production code still has
the private frontier theorem

- `OSToWightmanBoundaryValues.lean`, private theorem
  `bvt_W_swap_pairing_of_spacelike`.

The retired finite-height shell theorem `bvt_F_swapCanonical_pairing` is kept in
this document only as historical/fallback analysis.  After the #1065 route
audit and the local OS I §4.5 reread, the primary route must be anchored to the
paper's order of argument:

1. **OS-internal §4.5 continuation stage.**  Use E3 together with the
   already-constructed Fourier-Laplace / ACR(1) witness and Lorentz covariance
   to obtain the symmetric selected analytic continuation on the permuted
   forward-tube union.  In current Lean terms, the adjacent real-edge packet is
   only a local interface for proving the required `extendF` overlap equality;
   it is not a replacement proof route.
2. **External BHW/Jost stage.**  Formalize the Bargmann-Hall-Wightman and
   Jost boundary-value theorem as external analytic inputs: BHW enlarges the
   symmetric continuation to the complex-Lorentz saturated domain, and the Jost
   theorem converts that symmetric continuation into locality of the boundary
   distributions.
3. **OS-internal boundary transfer.**  Apply the selected boundary-value
   package to identify the boundary distributions with the reconstructed
   `bvt_W OS lgc` family and close R3.

The finite-shell packet remains a fallback only if we deliberately keep the
current private consumer unchanged.  Conversely, PET germ/channel monodromy is
not the next implementation target until the OS-internal §4.5 continuation
stage has a complete proof transcript.

This note supersedes older gap notes that were written before
`edge_of_the_wedge` was proved as a theorem.

This note should be read together with:
- `docs/os1_detailed_proof_audit.md`, Section 9,
- `docs/theorem3_os_route_blueprint.md` only for route discipline,
- `docs/edge_of_the_wedge_proof_plan.md` and
  `docs/edge_of_the_wedge_gap_analysis.md` only as historical reference.

### 0.0. OS §4.5 priority correction after #1065

Theorem 2 should not invert the structure of OS I §4.5.  The paper's locality
argument has OS-internal content before and after the BHW/Jost citations:

General route discipline for this blueprint: for theorems actually proved in
the OS papers, follow the OS proof closely.  External citations such as BHW may
be formalized independently in their own modules, and the known OS I error must
be corrected rather than reproduced, but OS-internal locality steps should be
documented as a faithful proof transcript of §4.5 before Lean implementation.

The local OS I text says the §4.5 proof proceeds as follows.  First, from E3
and the previously constructed equations `(4.1)`, `(4.12)`, and `(4.14)`, the
selected Wightman analytic function is symmetric and single-valued on the
permuted forward-tube domain `S'_n`.  Second, the Bargmann-Hall-Wightman theorem
extends that symmetric function to the complex-Lorentz saturation `S''_n`.
Third, the cited Jost theorem turns this symmetric analytic continuation into
local commutativity of the boundary distributions.

That paper ledger is the source of truth.  The current Lean structure
`SelectedAdjacentPermutationEdgeData` is acceptable only as a narrow
implementation bridge for the first sentence above: it supplies adjacent
`extendF` overlap equality so that the selected branch data can be glued into
`bvt_F_symmetric_PET_extension`.  If this interface starts to require more than
the OS §4.5 continuation argument provides, the interface should be changed
rather than the blueprint drifting away from the paper.

| Step | Content | Ownership in this formalization |
| --- | --- | --- |
| 1 | E3 + `(4.1)`, `(4.12)`, `(4.14)` produce the symmetric selected analytic continuation on the permuted forward-tube union `S'_n` | OS-internal; active target |
| 1a | adjacent `extendF` overlap equality / real-edge packet used by the current Lean branch-gluing interface | OS-internal implementation bridge, subordinate to Step 1 |
| 2 | BHW extends the symmetric continuation to the complex-Lorentz saturation `S''_n` | external BHW infrastructure |
| 3 | the cited Jost boundary theorem converts symmetric continuation into locality of boundary distributions | external Jost/SCV theorem plus OS boundary-value identification |
| 4 | identify the boundary distributions with `bvt_W OS lgc` and close R3 | OS-internal final theorem-2 bridge |

Paper-step to Lean-name ledger:

| OS §4.5 ingredient | Current / planned Lean surface |
| --- | --- |
| E3 symmetry of Euclidean Green functions | `OS.E3_symmetric`; selected-witness consequence `bvt_F_perm` |
| `(4.1)` ordered Euclidean relative-coordinate restriction | `bvt_euclidean_restriction`, `bvt_F_acrOne_package` |
| `(4.12)` Fourier-Laplace representation of the selected Wightman analytic function | `full_analytic_continuation_with_acr_symmetry_growth`, `bvt_F_holomorphic`, `bvt_boundary_values` |
| `(4.14)` Lorentz covariance / spectrum-side covariance | `bvt_F_restrictedLorentzInvariant_forwardTube`, then complex-Lorentz propagation for `extendF` |
| symmetric continuation on `S'_n` | `bvt_F_symmetric_PET_extension_of_adjacentEdgeData` or a more direct `bvt_F_symmetric_PET_extension` if the adjacent-edge interface is retired |
| BHW enlargement to `S''_n` | `BHW.bargmann_hall_wightman_theorem_of_adjacentBranchEquality` / non-circular sibling of the existing BHW theorem |
| Jost boundary theorem giving R3 | `bv_local_commutativity_transfer_of_symmetric_PET_boundary` |
| identification with the reconstructed family | `bvt_boundary_values`, `bv_local_commutativity_transfer_of_swap_pairing` only if the finite-shell fallback remains active |

Therefore the immediate target is not another PET-germ adapter.  In the current
Lean API, the next concrete target is construction of the adjacent edge packet,
but only because it is the smallest missing bridge into the OS §4.5 symmetric
continuation theorem:

```lean
theorem bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SelectedAdjacentPermutationEdgeData OS lgc n
```

The suffix `_of_two_le` is not cosmetic.  This is the implementation target for
the real-open OS45 edge packet in the `2 ≤ d` branch.  It should not be renamed
or wrapped as an all-`[NeZero d]` theorem unless a separate `d = 1` proof
constructs the same real-open fields.  If the `d = 1` proof instead uses a
complex edge, it belongs in a different theorem surface and should feed the
final locality theorem by a dimension-case split.

This theorem must provide both fields of `SelectedAdjacentPermutationEdgeData`:

1. `overlap_connected`: adjacent ET/swap-ET overlap connectedness, a BHW
   geometry lemma independent of OS.
2. `edge_witness`: a nonempty real-open adjacent Jost/ET overlap `V` and
   compact-test equality

   ```lean
   ∫ x, BHW.extendF (bvt_F OS lgc n)
       (BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
     =
   ∫ x, BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x
   ```

   for every compactly supported `φ` with `tsupport φ ⊆ V`.

The proof transcript for `edge_witness` must be complete before Lean
implementation resumes on this seam:

1. choose the exact adjacent real-open Jost set `V`;
2. prove `V` is open, connected, nonempty, and lies in both ET and swapped ET;
3. show `tsupport φ ⊆ V` makes `φ` an honest zero-diagonal Euclidean test;
4. use E3 on the permuted zero-diagonal test and the change-of-variables lemma
   to get the Euclidean Wick-edge compact pairing equality;
5. use `bvt_F_acrOne_package` plus the many-variable
   EOW/totally-real identity theorem to transport that Euclidean pairing
   equality to the real Jost edge for `extendF (bvt_F OS lgc n)`;
6. package the result into `SelectedAdjacentPermutationEdgeData`.

Resolved route decisions for this seam:

1. Do not rely on a global implication `BHW.JostSet -> ExtendedTube`, which is
   false for the current pairwise-spacelike repo predicate.  The selected
   adjacent edge theorem chooses a small real-open `V` with explicit
   `hV_jost`, `hV_ET`, `hV_swapET`, and ordered-sector fields.
2. The EOW theorem surface is branch-difference shaped.  The preferred
   implementation now shrinks the selected real-open ball into one local EOW
   chart and uses
   `os45_adjacent_branchDifferenceEnvelope_and_edge_exists_singleChart`, which
   returns the final `V` only after the EOW domain is known.
   The broader `SCV.differenceEnvelope_of_localBoundaryCharts` theorem remains
   a fallback only if this single-chart shrink fails.
3. The route constructs a pointwise holomorphic branch-difference envelope
   first, then uses compact-test Wick-edge zero with
   `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` to force
   the real-edge branch difference to vanish.  It does not assume raw
   continuity of `bvt_F OS lgc n` on real boundary points; the real trace is the
   continuous `extendF` trace.

#### Lean-shaped transcript for the OS edge supplier

The active proof-doc target can be decomposed into the following Lean-facing
lemmas.  This is the transcript that should be completed before attempting the
next production proof.

**A. Geometry and zero-diagonal preparation.**

The chosen edge `V` must lie in the current pairwise-spacelike `BHW.JostSet`
and in the two relevant ET real traces.  Pairwise Jost support is enough to
promote compactly supported tests to the honest OS-I zero-diagonal space,
because no Jost point is coincident:

```lean
theorem BHW.jostSet_disjoint_coincidenceLocus
    (d n : ℕ) :
    Disjoint (BHW.JostSet d n) (CoincidenceLocus d n)

theorem zeroDiagonal_of_tsupport_subset_jostOverlap
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport :
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    VanishesToInfiniteOrderOnCoincidence φ := by
  -- Prove `Disjoint (tsupport φ) (CoincidenceLocus d n)` using
  -- `hφ_tsupport`, `hV_jost`, and `BHW.jostSet_disjoint_coincidenceLocus`;
  -- then apply `VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint`.
```

The permutation action on zero-diagonal tests should use the existing
`reindexSchwartz` / `VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv`
in `Core.lean`; it must not use `ZeroDiagonalSchwartz.ofClassical` as a hidden
fallback:

```lean
def BHW.permuteZeroDiagonalSchwartz
    (σ : Equiv.Perm (Fin n))
    (f : ZeroDiagonalSchwartz d n) :
    ZeroDiagonalSchwartz d n :=
  ⟨BHW.permuteSchwartz (d := d) σ f.1,
    f.2.compCLMOfContinuousLinearEquiv σ⟩

@[simp] theorem BHW.permuteZeroDiagonalSchwartz_apply
    (σ : Equiv.Perm (Fin n)) (f : ZeroDiagonalSchwartz d n)
    (x : NPointDomain d n) :
    (BHW.permuteZeroDiagonalSchwartz (d := d) σ f).1 x =
      f.1 (fun k => x (σ k))
```

The adjacent real-open edge can use the existing local theorem
`BHW.exists_real_open_nhds_adjSwap`, but its seed point must be chosen from
actual OS/BHW adjacent Jost geometry **and** from a fixed Euclidean time-order
sector.  The time-order data is not optional: OS §4.5 starts from Euclidean
ordered/Wick points in the permuted forward-tube union, and the adjacent swap
usually moves the Wick point to a different permuted time-order sector.  Thus a
helper that returns only `V`, `hV_ET`, and `hV_swapET` is not enough for the
EOW branch-identification theorem.

The correct construction helper should export the fields needed by
`SelectedAdjacentPermutationEdgeData.edge_witness`, plus the fixed order used
on the Wick side:

```lean
theorem choose_os45_real_open_edge_for_adjacent_swap
    (hd : 2 ≤ d)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n)),
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
      (∀ x ∈ V, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ) ∧
      (∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
```

Do not replace this by a global theorem
`BHW.JostSet d n ⊆ {x | BHW.realEmbed x ∈ BHW.ExtendedTube d n}`; that
statement is false for the current `BHW.JostSet`.

Lean proof sketch for the time-order fields:

First isolate the seed theorem:

```lean
theorem adjacent_os45_seed_exists
    (hd : 2 ≤ d)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∃ (x0 : NPointDomain d n) (ρ : Equiv.Perm (Fin n)),
      x0 ∈ BHW.JostSet d n ∧
      BHW.realEmbed x0 ∈ BHW.ExtendedTube d n ∧
      BHW.realEmbed
        (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHW.ExtendedTube d n ∧
      x0 ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ ∧
      (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
```

Seed proof transcript:

1. Start from the checked adjacent-overlap witness theorem
   `adjacent_overlap_real_spacelike_witness_exists (d := d) hd i hi`.
   This already returns a real point `x` with the selected adjacent pair
   spacelike and both
   `BHW.realEmbed x ∈ BHW.ExtendedTube d n` and
   `BHW.realEmbed (x ∘ τ) ∈ BHW.ExtendedTube d n`, where
   `τ := Equiv.swap i ⟨i.val + 1, hi⟩`.
2. Strengthen the exported witness theorem, rather than re-proving the private
   internals of `AdjacentOverlapWitness.lean`, to expose the missing Jost field:

   ```lean
   theorem adjacent_overlap_real_jost_witness_exists
       (hd : 2 ≤ d) (i : Fin n) (hi : i.val + 1 < n) :
       ∃ x : NPointDomain d n,
         x ∈ BHW.JostSet d n ∧
         (∑ μ, minkowskiSignature d μ *
             (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0) ∧
         (∀ k : Fin n, x k 0 = 0) ∧
         BHW.realEmbed x ∈ BHW.ExtendedTube d n ∧
         BHW.realEmbed
           (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           BHW.ExtendedTube d n
   ```

   Proof source: the existing adjacent witness is built from
   `swapWitnessReal`, whose private proof already goes through
   `ForwardJostSet`; the public theorem should expose
   `forwardJostSet_subset_jostSet` at the same time as the ET fields.  This is
   a real theorem-surface improvement, not a wrapper: downstream OS §4.5 needs
   the `hV_jost` field.

   Lean proof transcript:

   1. use `swapWitnessReal (d := d) (n := n) hd i hi` as the witness;
   2. obtain `hd1 : 1 ≤ d` from `hd`;
   3. set
      `hxFJ := swapWitnessReal_mem_forwardJostSet (d := d) (n := n) hd i hi`;
   4. prove `x ∈ BHW.JostSet d n` by
      `BHW.forwardJostSet_subset_jostSet hd1 hxFJ`;
   5. prove the selected adjacent spacelike inequality by reusing the same
      `forwardJostSet_consec_spacelike` calculation already present in
      `adjacent_overlap_real_spacelike_witness_exists`;
   6. prove the zero-time field by `intro k; simp [swapWitnessReal]`;
   7. reuse `swapWitnessReal_mem_extendedTube` and
      `swapWitnessRealSwapped_mem_extendedTube`, rewriting the swapped real
      embedding with `[swapWitnessRealSwapped]`.

   This theorem should be added near
   `adjacent_overlap_real_spacelike_witness_exists` in
   `AdjacentOverlapWitness.lean`, because it deliberately publicizes facts
   already proved by that file's private witness construction.
3. Add the time-order field by a separate small-perturbation lemma around the
   chosen adjacent witness.  Do **not** state this as a theorem about an
   arbitrary nonempty open overlap: an open set can sit entirely at negative
   Euclidean times, while `OrderedPositiveTimeRegion` requires positive times.

   ```lean
   theorem exists_ordered_small_time_perturb_in_adjacent_overlap
       (hd : 2 ≤ d)
       (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
       (U : Set (NPointDomain d n))
       (hU_open : IsOpen U)
       (x : NPointDomain d n)
       (hxU : x ∈ U)
       (hx_time0 : ∀ k : Fin n, x k 0 = 0) :
       ∃ (x0 : NPointDomain d n) (ρ : Equiv.Perm (Fin n)),
         x0 ∈ U ∧
         x0 ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ ∧
         (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           EuclideanOrderedPositiveTimeSector (d := d) (n := n)
             ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
   ```

   Proof idea: use `hU_open.mem_nhds hxU` and the curve
   `xε k μ := if μ = 0 then ε * ((k : ℝ) + 1) else x k μ`.  For sufficiently
   small `ε > 0`, `xε ∈ U`; its Euclidean times are strictly positive and
   strictly increasing, so `ρ = 1` works.  The swapped ordered sector is then
   forced by the same ordered list and the identity `τ.symm * ρ`.  This lemma
   should cite the public definition `EuclideanOrderedPositiveTimeSector` and
   prove the ordering directly; it should not rely on a false density theorem
   for arbitrary open subsets.
4. Build the open overlap `U` from the strengthened witness and existing open
   sets:

   ```lean
   def adjacentOS45RawOverlap
       (d n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
       Set (NPointDomain d n) :=
     {x | x ∈ BHW.JostSet d n ∧
       BHW.realEmbed x ∈ BHW.ExtendedTube d n ∧
       BHW.realEmbed
         (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
         BHW.ExtendedTube d n}

   theorem isOpen_adjacentOS45RawOverlap :
       IsOpen (adjacentOS45RawOverlap d n i hi)
   ```

   Proof source: `BHW.isOpen_jostSet`, `BHW.isOpen_extendedTube`, continuity of
   `BHW.realEmbed`, and continuity of the finite-coordinate permutation map.
   Nonemptiness comes from `adjacent_overlap_real_jost_witness_exists`.

   Lean proof transcript for openness:

   1. rewrite `adjacentOS45RawOverlap` as an intersection of three preimages;
   2. use `BHW.isOpen_jostSet` for the first factor;
   3. use `BHW.isOpen_extendedTube.preimage` with continuity of
      `BHW.realEmbed` for the second factor;
   4. use `BHW.isOpen_extendedTube.preimage` with continuity of
      `fun x => BHW.realEmbed (fun k => x (τ k))` for the third factor;
   5. combine the three open sets with `IsOpen.inter`.

   Lean proof transcript for nonemptiness:

   1. obtain `x` from `adjacent_overlap_real_jost_witness_exists`;
   2. return `⟨x, hx_jost, hx_ET, hx_swapET⟩`.
5. After choosing an ordered point `x0` and `ρ`, use a **small connected open
   ball**, not a connected component, to define the final real edge `V`.
   The generic helper should be:

   ```lean
   theorem exists_connected_open_ball_subset
       {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
       {S : Set E} {x0 : E}
       (hS_open : IsOpen S) (hx0 : x0 ∈ S) :
       ∃ r : ℝ,
         0 < r ∧
         IsOpen (Metric.ball x0 r) ∧
         IsConnected (Metric.ball x0 r) ∧
         (Metric.ball x0 r).Nonempty ∧
         Metric.ball x0 r ⊆ S
   ```

   Proof transcript:

   1. from `hS_open.mem_nhds hx0`, obtain `r > 0` with
      `Metric.ball x0 r ⊆ S`;
   2. `IsOpen (Metric.ball x0 r)` is standard;
   3. `Metric.ball x0 r` is convex in a real normed vector space, hence
      preconnected/connected because it is nonempty;
   4. nonemptiness is witnessed by `x0`.

   In the actual selector, set

   ```lean
   S :=
     adjacentOS45RawOverlap d n i hi ∩
     EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ ∩
     {x | (fun k => x (τ k)) ∈
       EuclideanOrderedPositiveTimeSector (d := d) (n := n) (τ.symm * ρ)}
   ```

   Then apply the ball helper at the ordered point from
   `exists_ordered_small_time_perturb_in_adjacent_overlap`.

   The final selector theorem `choose_os45_real_open_edge_for_adjacent_swap`
   should take `V := Metric.ball x0 r`.  All exported fields are inherited from
   `V ⊆ S`; connectedness comes from the ball helper.  This avoids needing
   global connectedness of the whole raw overlap; only the
   `SelectedAdjacentPermutationEdgeData.overlap_connected` field separately
   uses the BHW connectedness theorem.
6. Do **not** extend this real-open-edge theorem from `2 ≤ d` to `[NeZero d]`
   by a large-spatial-slope argument.  The `d = 1` case is not a routine
   specialization; it is a different complex-edge problem.

   The replacement target should be a new, fully specified complex-edge chart
   packet for dimension one.  It is **not** implementation-ready yet, and it
   should not be represented by a placeholder theorem statement.  Before Lean
   work resumes on the all-dimensional theorem, the docs must say exactly what
   complex edge replaces the real-open `V`, how compact real Jost test supports
   are recovered as boundary values, and how the OS §4.5 EOW step reaches the
   real spacelike boundary in `d = 1`.

   The existing `adjacent_overlap_witness_exists_d1` gives a **complex**
   adjacent ET/swap-ET witness, not a real Jost seed with fixed Euclidean time
   order.  It can be mined for the explicit rapidity/Wick-rotation calculation,
   but it cannot be used as this theorem by projection to real or imaginary
   parts.  A naive real choice
   `x0 k = (ε * (k+1), L * (k+1))` proves the identity ordered sector and
   pairwise spacelike/Jost inequalities for `L >> ε`, but the adjacent-swapped
   consecutive spatial differences change orientation.  Thus its swapped ET
   membership is **not** a one-line `ForwardJostSet` consequence.

   Stress test for why the real theorem should not be targeted in `d = 1`:
   for `n = 2`, an adjacent swap sends the original consecutive difference
   `ζ₁ = x₁ - x₀` to `-ζ₁`.  The `d = 1` rapidity normal form in
   `D1OrbitSet.lean` says a real configuration in the real trace of one
   extended-tube sector has its consecutive spacelike differences in one
   light-cone orientation after a single complex rapidity.  The swapped
   configuration would require the opposite orientation for `ζ₁`.  Thus a
   single real `x0` cannot be expected to satisfy both real-trace ET fields.
   The production-safe action is therefore to keep
   `choose_os45_real_open_edge_for_adjacent_swap` as a `2 ≤ d` theorem and
   develop a separate `d = 1` complex-edge EOW chart if theorem 2 is to remain
   stated for all `[NeZero d]`.

   Audit of the current `d = 1` permutation-flow blocker:

   - `BHWPermutation/PermutationFlowBlocker.lean` contains the deferred theorem
     `blocker_iterated_eow_hExtPerm_d1_nontrivial` as a theorem-level `sorry`.
     This declaration is not an ad hoc placeholder: its production docstring
     records the dedicated `d = 1` numerical validation campaign and the exact
     BHW permutation-flow role it is intended to play.  The point here is only
     theorem-shape separation.  Its hypotheses include
     `hF_local_dist : IsLocallyCommutativeWeak 1 W`, so it is circular for the
     current `E -> R` theorem-2 locality proof.  It may be useful downstream in
     a Wightman/BHW permutation-flow proof, but it cannot be cited as the
     non-circular OS45 supplier.
   - Likewise, `blocker_isConnected_permSeedSet_nontrivial` is a carefully
     documented geometric/topological blocker with explicit `d = 1,n = 2`
     numerical support in the file docstring.  It supports the BHW
     permutation-flow route.  It does not by itself supply the OS45 real-open
     adjacent edge `V`, because `SelectedAdjacentPermutationEdgeData.edge_witness`
     asks for a compact-test OS edge equality on a chosen real-open
     Jost/ET/swap-ET overlap.
   - `BHWReducedExtension.lean` contains the explicit axiom
     `reduced_bargmann_hall_wightman_of_input`, stated for all `[NeZero d]`.
     This is a generic reduced BHW bridge and therefore includes `d = 1`, but
     using it would move the proof to the reduced-BHW fallback route.  It is
     not the OS I §4.5 complex-edge chart packet and should not be silently
     substituted for that missing dimension-one argument.
   - If we deliberately choose an axiomatic `d = 1` closure for theorem 2, the
     axiom must be documented as a new or explicitly reused trust boundary and
     must be non-circular: it should be pure BHW/SCV complex-edge geometry or a
     reduced BHW extension theorem, not a theorem whose hypotheses already
     include local commutativity of the target Wightman family.

   Dimension-split implementation invariant:

   - In the `2 ≤ d` branch, the current target really is
     `SelectedAdjacentPermutationEdgeData`.  Its real-open witness `V` is the
     interface consumed by the existing adjacent-overlap propagation theorem in
     `OSToWightmanSelectedWitness.lean`.
   - In the `d = 1` branch, the validated `PermutationFlowBlocker.lean`
     theorems put the dimension-one case on equal footing with `d ≥ 2` only
     for the deferred BHW/permutation-flow endgame.  They do not by themselves
     provide the non-circular OS §4.5 supplier.
   - Therefore the all-dimensional theorem-2 proof must not say “use the
     `2 ≤ d` real-edge packet with `d = 1`.”  It has two honest options:
     either prove a dimension-one real/complex edge theorem strong enough to
     fill the same downstream locality role, or prove a parallel direct
     dimension-one boundary-locality theorem.
   - If a dedicated `d = 1` argument actually constructs a real-open
     Jost/ET/swap-ET edge satisfying the fields of
     `SelectedAdjacentPermutationEdgeData.edge_witness`, then it may feed the
     same adjacent-edge/PET machinery.  But that is a new theorem, not a
     consequence of `JostWitnessGeneralSigma.jostWitness_exists`, not a
     projection of `adjacent_overlap_witness_exists_d1`, and not a use of
     `blocker_iterated_eow_hExtPerm_d1_nontrivial`.
   - If the dimension-one construction is genuinely complex-edge rather than
     real-open-edge, then it should not be forced through
     `SelectedAdjacentPermutationEdgeData`.  The proof docs must instead name a
     separate theorem such as

     ```lean
     theorem bvt_locally_commutative_boundary_route_of_one
         (OS : OsterwalderSchraderAxioms 1)
         (lgc : OSLinearGrowthCondition 1 OS) :
         IsLocallyCommutativeWeak 1 (bvt_W OS lgc)
     ```

     whose proof uses OS E3, the selected analytic witness, the
     one-dimensional complex-edge/EOW packet, and `bvt_boundary_values`, but no
     hypothesis of the form
     `IsLocallyCommutativeWeak 1 (bvt_W OS lgc)`.

   Lean-readiness consequence: the `2 ≤ d` branch can proceed toward
   implementation once the adjacent branch-difference EOW packet below is
   complete.  The all-`[NeZero d]` theorem is **not** implementation-ready
   until either the `d = 1` real-open edge theorem or the direct
   `bvt_locally_commutative_boundary_route_of_one` transcript is specified to
   the same level of detail.

   Dimension-one proof-doc target surfaces:

   The all-dimensional closure should choose one of the following branches
   before any production Lean is written for `d = 1`.

   **D1-R, real-open variant.**  Prove a theorem with the same fields as the
   `2 ≤ d` edge selector, but by a dimension-one argument:

   ```lean
   theorem choose_os45_real_open_edge_for_adjacent_swap_d1
       (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
       ∃ (V : Set (NPointDomain 1 n)) (ρ : Equiv.Perm (Fin n)),
         IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
         (∀ x ∈ V, x ∈ BHW.JostSet 1 n) ∧
         (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube 1 n) ∧
         (∀ x ∈ V,
           BHW.realEmbed
             (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
             BHW.ExtendedTube 1 n) ∧
         (∀ x ∈ V,
           x ∈ EuclideanOrderedPositiveTimeSector (d := 1) (n := n) ρ) ∧
         (∀ x ∈ V,
           (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
             EuclideanOrderedPositiveTimeSector (d := 1) (n := n)
               ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
   ```

   If this theorem is true, the rest of the `2 ≤ d` OS45 edge transcript can be
   replayed in dimension one, producing

   ```lean
   theorem bvt_F_selectedAdjacentPermutationEdgeData_from_OS_d1
       (OS : OsterwalderSchraderAxioms 1)
       (lgc : OSLinearGrowthCondition 1 OS)
       (n : ℕ) :
       SelectedAdjacentPermutationEdgeData OS lgc n
   ```

   This route is implementation-ready only after the real-open theorem above
   has a proof transcript from `D1OrbitSet.lean` / `IndexSetD1.lean` or a
   direct one-dimensional OS45 geometry argument.  The existing validated
   `PermutationFlowBlocker.lean` blockers do not prove it.

   **D1-C, complex-edge/PET variant.**  If the real-open edge theorem is false
   or not the right OS §4.5 object in dimension one, the target should be the
   symmetric PET extension itself, not `SelectedAdjacentPermutationEdgeData`:

   ```lean
   theorem bvt_F_symmetric_PET_extension_of_OS_d1_complexEdge
       (OS : OsterwalderSchraderAxioms 1)
       (lgc : OSLinearGrowthCondition 1 OS)
       (n : ℕ) :
       ∃ Fext : (Fin n → Fin (1 + 1) → ℂ) → ℂ,
         DifferentiableOn ℂ Fext (BHW.PermutedExtendedTube 1 n) ∧
         (∀ z ∈ ForwardTube 1 n, Fext z = bvt_F OS lgc n z) ∧
         (∀ (Λ : ComplexLorentzGroup 1) z,
           z ∈ BHW.PermutedExtendedTube 1 n →
           Fext (BHW.complexLorentzAction Λ z) = Fext z) ∧
         (∀ (σ : Equiv.Perm (Fin n)) z,
           z ∈ BHW.PermutedExtendedTube 1 n →
           Fext (fun k => z (σ k)) = Fext z)
   ```

   Proof transcript for D1-C:

   1. Use `bvt_F_holomorphic`, `bvt_F_perm`,
      `bvt_F_complexLorentzInvariant_forwardTube`, and
      `bvt_boundary_values`; do not use
      `IsLocallyCommutativeWeak 1 (bvt_W OS lgc)`.
   2. Replace the `2 ≤ d` real-open adjacent edge by a one-dimensional
      complex-edge chart packet.  The packet must state exactly which
      dimension-one edge/domain replaces `V`, how the two adjacent branches
      have a common OS boundary value there, and how the EOW/identity theorem
      propagates equality across adjacent sector overlaps.
   3. Prove adjacent selected PET branch compatibility in dimension one from
      that complex-edge packet.  This theorem may use the validated
      `D1OrbitSet.lean` / `IndexSetD1.lean` geometry, but it may not call
      `blocker_iterated_eow_hExtPerm_d1_nontrivial` unless the
      `hF_local_dist` hypothesis has been supplied by a non-circular theorem
      already proved for the selected OS family.
   4. Glue the finite sector cover exactly as in the `2 ≤ d` route, yielding
      the symmetric PET extension above.
   5. Apply `bv_local_commutativity_transfer_of_symmetric_PET_boundary` with
      `bvt_boundary_values` to obtain:

      ```lean
      theorem bvt_locally_commutative_boundary_route_of_one
          (OS : OsterwalderSchraderAxioms 1)
          (lgc : OSLinearGrowthCondition 1 OS) :
          IsLocallyCommutativeWeak 1 (bvt_W OS lgc)
      ```

   D1-C is currently the safer proof-doc target if the real-open edge theorem
   remains geometrically unclear, because it follows the OS paper statement
   “construct a symmetric continuation on `S'_n`” directly instead of forcing a
   dimension-one complex edge through a real-open-edge data structure.

   Minimum missing theorem slots for D1-C:

   ```lean
   theorem d1_selectedPETBranch_adjacent_eq_on_complexEdgeOverlap
       (OS : OsterwalderSchraderAxioms 1)
       (lgc : OSLinearGrowthCondition 1 OS)
       (n : ℕ)
       (π : Equiv.Perm (Fin n))
       (i : Fin n) (hi : i.val + 1 < n)
       (z : Fin n → Fin (1 + 1) → ℂ)
       (hzπ : z ∈ BHW.permutedExtendedTubeSector 1 n π)
       (hzπswap :
         z ∈ BHW.permutedExtendedTubeSector 1 n
           (π * Equiv.swap i ⟨i.val + 1, hi⟩)) :
       bvt_selectedPETBranch (d := 1) OS lgc n
           (π * Equiv.swap i ⟨i.val + 1, hi⟩) z =
         bvt_selectedPETBranch (d := 1) OS lgc n π z
   ```

   This theorem is the dimension-one analogue of
   `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`.  It is the correct
   consumer for PET gluing in D1-C, because it proves adjacent branch equality
   directly on sector overlaps without first constructing a real-open
   `SelectedAdjacentPermutationEdgeData.edge_witness`.

   Its proof must be decomposed before Lean implementation into honest local
   theorem slots, not placeholder statements:

   1. a concrete one-dimensional complex chart/domain theorem crossing the
      adjacent `π` / `π * swap` sectors;
   2. branch holomorphy for the two selected OS PET branches on that chart;
   3. a common OS boundary-value theorem from E3, `(4.1)`, `(4.12)`, and
      `(4.14)`, with no locality hypothesis;
   4. a one-dimensional EOW/identity theorem that turns the common boundary
      value into equality of the two branch germs;
   5. a connectedness or monodromy theorem propagating the local germ equality
      to the full adjacent sector overlap containing `z`.
4. Once `adjacent_os45_seed_exists` is proved, first intersect the open
   neighborhoods of:
   `BHW.JostSet d n`,
   `{x | BHW.realEmbed x ∈ BHW.ExtendedTube d n}`,
   `{x | BHW.realEmbed (x ∘ τ) ∈ BHW.ExtendedTube d n}`,
   `EuclideanOrderedPositiveTimeSector ρ`, and
   the swapped ordered sector.  The seed belongs to all five sets, so the
   intersection is an open neighborhood of the seed.  Then choose a small open
   ball around the seed whose closed or open ball is contained in that
   intersection, and take this ball as `V`.  This gives `IsOpen V`,
   `IsConnected V`, and `V.Nonempty`, while all five membership fields follow
   by subset transitivity.  The connectedness is needed only by the
   local-to-global EOW gluing proof; `SelectedAdjacentPermutationEdgeData`
   itself does not store it.
5. The swapped ordered-sector field uses the identity
   `(fun k => (fun j => x (τ j)) ((τ.symm * ρ) k)) = fun k => x (ρ k)`.
   In the final Lean proof this should be a small simp lemma for adjacent
   swaps and permutation multiplication orientation.

The other geometry field of `SelectedAdjacentPermutationEdgeData` is external
BHW infrastructure:

```lean
theorem BHW.isConnected_adjSwapExtendedOverlap
    [NeZero d]
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    IsConnected
      {z : Fin n → Fin (d + 1) → ℂ |
        z ∈ BHW.ExtendedTube d n ∧
          BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
            BHW.ExtendedTube d n}
```

The existing route to this statement is through
`BHW.isConnected_adjSwapExtendedOverlap_of_forwardOverlapConnected` and the
real-double-coset generation theorem for the adjacent forward-overlap index
set.  This is BHW work, but it is a small external geometry lemma, not the
PET-germ monodromy project.

**B. E3 gives the Euclidean Wick-edge compact equality.**

Let `τ := Equiv.swap i ⟨i.val + 1, hi⟩`.  For any compactly supported test with
`tsupport φ ⊆ V`, first build

```lean
φZ : ZeroDiagonalSchwartz d n := ⟨φ,
  zeroDiagonal_of_tsupport_subset_jostOverlap V hV_jost φ hφ_tsupport⟩
```

Then apply E3 to `φZ` and the inverse-permuted test
`BHW.permuteZeroDiagonalSchwartz τ.symm φZ`.  The inverse is intentional:
after the change of variables it produces the desired branch
`x ↦ bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k)))`.

```lean
theorem bvt_F_euclidean_adjacent_branch_pairing_eq_from_E3
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport :
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (fun k => wickRotatePoint (x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) *
          φ x
      =
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x := by
  -- 1. construct `φZ`;
  -- 2. set `ψZ := BHW.permuteZeroDiagonalSchwartz τ.symm φZ`;
  -- 3. use `OS.E3_symmetric n τ.symm φZ ψZ`;
  -- 4. rewrite both Schwinger values by
  --    `bvt_euclidean_restriction OS lgc n`;
  -- 5. use `BHW.integral_perm_eq_self τ.symm` to move from
  --    `φ (x ∘ τ.symm)` to the branch `wick(x ∘ τ)`.
```

This is the OS §4.5 E3 step in compact-test form.  It uses only OS-internal
data plus the already-selected Euclidean reproduction theorem for `bvt_F`.

**C. ACR(1)/EOW transports the Euclidean equality to the real Jost edge.**

This is the remaining OS-internal analytic seam.  Since
`AnalyticContinuationRegion d n 1` is the positive-time-difference tube, the
real Jost edge is not obtained by simply proving
`realEmbed x ∈ AnalyticContinuationRegion d n 1`.  The OS §4.5 argument uses an
EOW/BHW envelope connecting the Euclidean Wick section to the real Jost edge.
Make that envelope explicit as data first:

```lean
structure AdjacentOSEOWEnvelope
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (τ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n)) where
  U : Set (Fin n → Fin (d + 1) → ℂ)
  U_open : IsOpen U
  U_connected : IsConnected U
  F_id : (Fin n → Fin (d + 1) → ℂ) → ℂ
  F_perm : (Fin n → Fin (d + 1) → ℂ) → ℂ
  F_id_holo : DifferentiableOn ℂ F_id U
  F_perm_holo : DifferentiableOn ℂ F_perm U
  wick_mem :
    ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U
  real_mem :
    ∀ x ∈ V, BHW.realEmbed x ∈ U
  wick_id :
    ∀ x ∈ V,
      F_id (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k))
  wick_perm :
    ∀ x ∈ V,
      F_perm (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k)))
  real_id :
    ∀ x ∈ V,
      F_id (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
  real_perm :
    ∀ x ∈ V,
      F_perm (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (τ k)))
```

This two-branch structure is not meant to hide the theorem, but it is stronger
than the current edge-data consumer needs.  It is safe only if both branches are
constructed as genuine OS §4.5 analytic continuations.  The sharper active
target below is the branch-difference envelope, because OS §4.5 transports the
zero of an adjacent branch difference rather than identifying one Wick value
with one real-time value.  If we keep the two-branch record, its existence
theorem is:

```lean
theorem adjacent_osEOWEnvelope_exists_from_OS45
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (ρ : Equiv.Perm (Fin n))
    (hV_open : IsOpen V)
    (hV_connected : IsConnected V)
    (hV_nonempty : V.Nonempty)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V,
      BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_swapET : ∀ x ∈ V,
      BHW.realEmbed
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHW.ExtendedTube d n)
    (hV_ordered : ∀ x ∈ V,
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (hV_swap_ordered : ∀ x ∈ V,
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
    Nonempty
      (AdjacentOSEOWEnvelope (d := d) OS lgc n
        (Equiv.swap i ⟨i.val + 1, hi⟩) V)
```

Paper-faithful proof transcript for this theorem:

1. Set `τ := Equiv.swap i ⟨i.val + 1, hi⟩`.  The theorem is the adjacent
   localization of OS I §4.5's first sentence: E3 plus `(4.1)`, `(4.12)`, and
   `(4.14)` give a symmetric selected analytic continuation on the permuted
   forward-tube union.  It must not be proved by assuming Wightman locality or
   by invoking the later PET monodromy theorem.
2. Use the selected witness facts already present in production:
   `bvt_F_holomorphic`, `bvt_F_acrOne_package`, `bvt_F_perm`,
   `bvt_F_translationInvariant`, and
   `bvt_F_restrictedLorentzInvariant_forwardTube`.  In paper language these
   are the Lean names for the Fourier-Laplace construction `(4.12)`, the
   Wightman distribution definition `(4.13)`, Lorentz covariance `(4.14)`, and
   Euclidean symmetry E3 after the selected-witness choice.
3. The ordered-sector hypotheses are essential.  From `hV_ordered`,
   `wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector` gives

   ```lean
   (fun k => wickRotatePoint (x (ρ k))) ∈ ForwardTube d n.
   ```

   From `hV_swap_ordered`, the same theorem gives the forward-tube membership
   for the swapped Wick configuration in the order
   `τ.symm * ρ`.  These two memberships are the Lean version of OS's
   permuted forward-tube domain `S'_n`; without them the theorem would be an
   overstatement about arbitrary Jost/ET neighborhoods.
4. Prove the local OS §4.5 envelope and final edge witness, preferably via the
   combined single-chart theorem
   `os45_adjacent_branchDifferenceEnvelope_and_edge_exists_singleChart`.
   The older fixed-`V` branch-difference theorem
   `os45_adjacent_branchDifferenceEnvelope_exists` is now a fallback only if
   the generic local-chart gluing route is used.  The stronger optional
   two-branch theorem is `adjacent_osEOWEnvelope_exists_from_OS45`.  Do **not**
   split off a weak
   geometry theorem saying only that there is an open connected `U` containing
   the Wick edge and the two real edges: `U = Set.univ` would satisfy such a
   statement and it would not encode any EOW continuation content.  A split is
   acceptable only if the geometric lemma carries the analytic source-domain
   data needed to construct the holomorphic branches.
5. If using the stronger two-branch theorem, construct `U`, `F_id`, and
   `F_perm` by the OS §4.5 analytic continuation, not by arbitrary choice.  The
   proof obligation is exactly:

   ```lean
   ∃ U F_id F_perm,
     IsOpen U ∧ IsConnected U ∧
     DifferentiableOn ℂ F_id U ∧
     DifferentiableOn ℂ F_perm U ∧
     (∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U) ∧
     (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
     (∀ x ∈ V,
       F_id (fun k => wickRotatePoint (x k)) =
         bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
     (∀ x ∈ V,
       F_perm (fun k => wickRotatePoint (x k)) =
         bvt_F OS lgc n
           (fun k =>
             wickRotatePoint
               (x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))) ∧
     (∀ x ∈ V,
       F_id (BHW.realEmbed x) =
         BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) ∧
     (∀ x ∈ V,
       F_perm (BHW.realEmbed x) =
         BHW.extendF (bvt_F OS lgc n)
           (BHW.realEmbed
             (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))))
   ```

   This is the exact mathematical content of the OS §4.5 branch-identification
   step in the current Lean vocabulary.  Its proof uses the selected
   Fourier-Laplace continuation and uniqueness of analytic continuation from
   the Euclidean Wick edge to the Jost edge.  It is allowed to cite or prove a
   standard SCV/EOW theorem, but it may not mention `IsLocallyCommutativeWeak`
   or consume theorem-2 locality.

   The branch origins must be recorded in the proof, because this is where a
   common false shortcut can enter.  Let
   `τ := Equiv.swap i ⟨i.val + 1, hi⟩` and `ρτ := τ.symm * ρ`.

   - For `x ∈ V`, `hV_ordered` gives
     `(fun k => wickRotatePoint (x (ρ k))) ∈ ForwardTube d n`.  The identity
     Wick branch is therefore the selected forward-tube value after reordering
     by `ρ`, transported back to the unpermuted Wick point by `bvt_F_perm`.
   - For the swapped configuration `xτ := fun k => x (τ k)`,
     `hV_swap_ordered` gives
     `(fun k => wickRotatePoint (xτ (ρτ k))) ∈ ForwardTube d n`; using
     `ρτ = τ.symm * ρ`, this is the same ordered Wick configuration as
     `fun k => wickRotatePoint (x (ρ k))`.  The permuted Wick branch is
     transported back to `fun k => wickRotatePoint (xτ k)` by `bvt_F_perm`.
   - Do **not** require
     `fun k => wickRotatePoint (x (τ k)) ∈ ForwardTube d n`; for an adjacent
     swap this generally contradicts the strict time ordering.  Do **not**
     require it to be in the ordinary `ExtendedTube` either.  OS §4.5 first
     lives on the permuted forward-tube union `S'_n`, and BHW/Jost/EOW is what
     relates that union to the real Jost/extended-tube edge.
   - On the real edge, the two branches must be the BHW/Jost continuations
     `BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)` and
     `BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed (fun k => x (τ k)))`.
     This real-edge identification is analytic content, not a definitional
     rewrite from the Wick-side branch.

   The implementation should expose the preceding paragraph through a
   two-chart theorem, not by trying to guess values of `F_id` and `F_perm`
   pointwise.  The source charts are:

   ```lean
   def OS45WickChartDomain
       (σ ρσ : Equiv.Perm (Fin n)) :
       Set (Fin n → Fin (d + 1) → ℂ) :=
     {z | BHW.permAct (d := d) ρσ
         (BHW.permAct (d := d) σ z) ∈ ForwardTube d n}

   def OS45RealChartDomain
       (σ : Equiv.Perm (Fin n)) :
       Set (Fin n → Fin (d + 1) → ℂ) :=
     {z | BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n}

   def OS45WickChart
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : ℕ)
       (σ ρσ : Equiv.Perm (Fin n)) :
       (Fin n → Fin (d + 1) → ℂ) → ℂ :=
     fun z =>
       bvt_F OS lgc n
         (BHW.permAct (d := d) ρσ
           (BHW.permAct (d := d) σ z))

   def OS45RealChart
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : ℕ)
       (σ : Equiv.Perm (Fin n)) :
       (Fin n → Fin (d + 1) → ℂ) → ℂ :=
     fun z =>
       BHW.extendF (bvt_F OS lgc n)
         (BHW.permAct (d := d) σ z)
   ```

   For `σ = 1`, the ordered label is `ρ`.  For the adjacent-swapped branch,
   `σ = τ` and the ordered label is `ρτ := τ.symm * ρ`.  On the Wick section,
   the key simplification is

   ```lean
   BHW.permAct (d := d) ρτ
       (BHW.permAct (d := d) τ
         (fun k => wickRotatePoint (x k)))
     =
   BHW.permAct (d := d) ρ
       (fun k => wickRotatePoint (x k))
   ```

   because `τ (ρτ k) = ρ k`.  Thus both Wick charts are represented on the
   same ordered forward-tube point.  The identities in the
   `AdjacentOSEOWEnvelope` record then follow from `bvt_F_perm`, not from a
   false claim that `wick(x ∘ τ)` itself lies in the ordinary forward tube.

   The acceptable split theorem is therefore the following chart-carrying
   statement.  It is not wrapper-shaped, because it carries the actual analytic
   charts whose restrictions must be glued by the OS §4.5 EOW/ACR argument:

   ```lean
   theorem os45_adjacent_twoChartEnvelope_exists
       (OS : OsterwalderSchraderAxioms d)
       (lgc : OSLinearGrowthCondition d OS)
       (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
       (V : Set (NPointDomain d n))
       (ρ : Equiv.Perm (Fin n))
       (hV_open : IsOpen V)
       (hV_connected : IsConnected V)
       (hV_nonempty : V.Nonempty)
       (hV_ordered : ∀ x ∈ V,
         x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
       (hV_swap_ordered : ∀ x ∈ V,
         (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           EuclideanOrderedPositiveTimeSector (d := d) (n := n)
             ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
       (hV_ET : ∀ x ∈ V,
         BHW.realEmbed x ∈ BHW.ExtendedTube d n)
       (hV_swapET : ∀ x ∈ V,
         BHW.realEmbed
           (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           BHW.ExtendedTube d n) :
       ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
         (F_id F_perm : (Fin n → Fin (d + 1) → ℂ) → ℂ),
         IsOpen U ∧ IsConnected U ∧
         DifferentiableOn ℂ F_id U ∧
         DifferentiableOn ℂ F_perm U ∧
         (∀ x ∈ V,
           (fun k => wickRotatePoint (x k)) ∈ U ∩
             OS45WickChartDomain (d := d) (n := n) 1 ρ) ∧
         (∀ x ∈ V,
           BHW.realEmbed x ∈ U ∩
             OS45RealChartDomain (d := d) (n := n) 1) ∧
         (∀ x ∈ V,
           (fun k => wickRotatePoint (x k)) ∈ U ∩
             OS45WickChartDomain (d := d) (n := n)
               (Equiv.swap i ⟨i.val + 1, hi⟩)
               ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) ∧
         (∀ x ∈ V,
           BHW.realEmbed x ∈ U ∩
             OS45RealChartDomain (d := d) (n := n)
               (Equiv.swap i ⟨i.val + 1, hi⟩)) ∧
         (Set.EqOn F_id
           (OS45WickChart (d := d) OS lgc n 1 ρ)
           (U ∩ OS45WickChartDomain (d := d) (n := n) 1 ρ)) ∧
         (Set.EqOn F_id
           (OS45RealChart (d := d) OS lgc n 1)
           (U ∩ OS45RealChartDomain (d := d) (n := n) 1)) ∧
         (Set.EqOn F_perm
           (OS45WickChart (d := d) OS lgc n
             (Equiv.swap i ⟨i.val + 1, hi⟩)
             ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
           (U ∩ OS45WickChartDomain (d := d) (n := n)
             (Equiv.swap i ⟨i.val + 1, hi⟩)
             ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))) ∧
         (Set.EqOn F_perm
           (OS45RealChart (d := d) OS lgc n
             (Equiv.swap i ⟨i.val + 1, hi⟩))
           (U ∩ OS45RealChartDomain (d := d) (n := n)
             (Equiv.swap i ⟨i.val + 1, hi⟩)))
   ```

   Proof transcript for `os45_adjacent_twoChartEnvelope_exists`:

   - `OS45WickChartDomain σ ρσ` is open because it is the preimage of
     `ForwardTube d n` under a continuous coordinate permutation.  Its Wick
     membership fields are exactly `hV_ordered` and `hV_swap_ordered` passed
     through `wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector`.
   - `OS45RealChartDomain σ` is open because it is the preimage of
     `BHW.ExtendedTube d n` under a continuous coordinate permutation.  Its
     real membership fields are exactly `hV_ET` and `hV_swapET`.
   - The Wick charts are holomorphic on their Wick chart domains by
     `bvt_F_holomorphic` composed with the coordinate permutations.
   - The real charts are holomorphic on their real chart domains by
     `BHW.extendF_holomorphicOn`, using
     `bvt_F_holomorphic` and
     `bvt_F_complexLorentzInvariant_forwardTube`.
   - Do not try to prove a one-branch identity
    `OS45WickChart σ ρσ = OS45RealChart σ`, either from
    `BHW.extendF_eq_on_forwardTube` or from the OS Fourier-Laplace formula.
    That would be the same kind of Euclidean-vs-Minkowski value comparison
    forbidden elsewhere in this project: a Wick value at
    `fun k => wickRotatePoint (x k)` is not the real-time boundary value at
    `BHW.realEmbed x`.  The OS §4.5 argument transports **equality of two
    adjacent branches**, not equality of each branch with itself on two
    different sections.
   - The correct EOW/ACR object is therefore the adjacent branch difference

    ```lean
    H_wick z =
      OS45WickChart OS lgc n τ (τ.symm * ρ) z -
      OS45WickChart OS lgc n 1 ρ z

    H_real z =
      OS45RealChart OS lgc n τ z -
      OS45RealChart OS lgc n 1 z
    ```

    OS E3 plus `(4.1)`, `(4.12)`, and `(4.14)` show that the Wick-side
    difference has zero compact-test pairing on the ordered Euclidean edge.
    The OS §4.5 EOW/BHW step constructs a single holomorphic difference
    witness whose Wick-edge trace is `H_wick` and whose real-Jost trace is
    `H_real`.  Only after this common difference witness exists do we use
    the totally-real/distributional identity theorem to conclude that
    `H_real` vanishes on the real edge.
   - The common `U` for the branch-difference witness must be a connected
    envelope containing both the Wick edge and the real Jost edge for the same
    already-chosen real-open set `V`.  Its nonemptiness is supplied by
    `hV_nonempty`.  The real-open edge supplied by
    `choose_os45_real_open_edge_for_adjacent_swap` must already be chosen
    small enough that both edge maps land in this component; the envelope
    theorem must not silently replace `V` by a smaller set after the compact
    support hypothesis has been fixed.  This is why the edge-selection helper
    and the envelope theorem both take `hV_open`, `hV_connected`, and
    `hV_nonempty`, not just a single base point.
   - The theorem may cite a standard SCV EOW result, but the result must have
     these chart restrictions as hypotheses/conclusions.  A theorem producing
     only an open connected set containing the edges is not enough.

   With this theorem in hand, the edge supplier should either fill the existing
   two-branch `AdjacentOSEOWEnvelope` honestly or, preferably, fill the sharper
   `AdjacentOSEOWDifferenceEnvelope` below.  The difference packet is closer to
   the actual consumer because the downstream proof only needs the real-edge
   adjacent difference to vanish.

   The precise Euclidean distributional input to the chart-gluing theorem is a
   **branch-difference zero statement**, not a one-branch Wick-to-real
   comparison.  A Lean-ready form is:

  ```lean
  theorem os45_adjacent_wick_branchDifference_pairing_zero
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ)
      (i : Fin n) (hi : i.val + 1 < n)
      (V : Set (NPointDomain d n))
      (ρ : Equiv.Perm (Fin n))
      (hV_ordered : ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
      (hV_swap_ordered : ∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            (OS45WickChart (d := d) OS lgc n
                (Equiv.swap i ⟨i.val + 1, hi⟩)
                ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
                (fun k => wickRotatePoint (x k)) -
              OS45WickChart (d := d) OS lgc n 1 ρ
                (fun k => wickRotatePoint (x k))) * φ x
          = 0
  ```

  This is the OS §4.5 E3 step in chart language.  It is essentially the
  existing planned theorem
  `bvt_F_euclidean_adjacent_branch_pairing_eq_from_E3`, with the chart
  definitions unfolded.  Its proof is:

  1. set `τ := Equiv.swap i ⟨i.val + 1, hi⟩` and
     `ρτ := τ.symm * ρ`;
  2. rewrite the two Wick-chart integrands as
     `bvt_F OS lgc n (BHW.permAct ρτ (BHW.permAct τ (wick x)))`
     and `bvt_F OS lgc n (BHW.permAct ρ (wick x))`;
  3. use `τ (ρτ k) = ρ k` to identify the two ordered Wick configurations;
  4. apply `bvt_F_perm` / E3 symmetry and support-zero bookkeeping.

  The hard OS §4.5 analytic step should likewise be stated for this branch
  difference.  The generic fixed-`V` fallback theorem is:

  ```lean
  theorem os45_adjacent_branchDifferenceEnvelope_exists
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (V : Set (NPointDomain d n))
      (ρ : Equiv.Perm (Fin n))
      (hV_open : IsOpen V)
      (hV_connected : IsConnected V)
      (hV_nonempty : V.Nonempty)
      (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
      (hV_ordered : ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
      (hV_swap_ordered : ∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
      (hV_ET : ∀ x ∈ V,
        BHW.realEmbed x ∈ BHW.ExtendedTube d n)
      (hV_swapET : ∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n) :
      ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
        (H : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        IsOpen U ∧ IsConnected U ∧
        DifferentiableOn ℂ H U ∧
        (∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U) ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
        (∀ x ∈ V,
          H (fun k => wickRotatePoint (x k)) =
            OS45WickChart (d := d) OS lgc n
              (Equiv.swap i ⟨i.val + 1, hi⟩)
              ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
              (fun k => wickRotatePoint (x k)) -
            OS45WickChart (d := d) OS lgc n 1 ρ
              (fun k => wickRotatePoint (x k))) ∧
        (∀ x ∈ V,
          H (BHW.realEmbed x) =
            OS45RealChart (d := d) OS lgc n
              (Equiv.swap i ⟨i.val + 1, hi⟩) (BHW.realEmbed x) -
            OS45RealChart (d := d) OS lgc n 1 (BHW.realEmbed x))
  ```

  This theorem is not a wrapper: it is the exact OS §4.5 analytic-continuation
  content needed by the current Lean edge-data interface.  It says the adjacent
  Wick-branch difference and the adjacent real-Jost `extendF` difference are
  restrictions of one holomorphic function on a connected envelope.  It never
  asserts that a single Wick value equals a single real-time value.

  The SCV/BHW input behind this theorem must also be difference-shaped.
  The previous packet
  `SCV.LocalTwoChartEOWGeometry D_wick D_real V` with
  `P ∩ D_real ⊆ TubeDomain (-C)` is false as stated: `D_real` contains the real
  edge point itself, while `TubeDomain (-C)` excludes real points because
  `0 ∉ C`.  The corrected local packet should instead say that the real branch
  is holomorphic on a neighborhood of the real edge and contains an opposite
  wedge used for EOW; the whole real branch domain is **not** mapped into that
  opposite wedge.

  Geometry alone is still not enough.  A theorem with arbitrary holomorphic
  `H_wick` and `H_real`, plus only local wedge geometry and Wick-side
  compact-test zero, would be false: take `H_wick = 0` and `H_real = 1`.  The
  packet must carry the **common boundary-value compatibility** of the two
  branch differences on the EOW real edge.  It must not carry the final glued
  envelope as a structure field: during active development that would hide the
  real blocker in a data payload.  A Lean-facing corrected hypothesis shape is:

  ```lean
  structure SCV.LocalDifferenceEOWChartData
      (D_wick D_real : Set (Fin n → Fin (d + 1) → ℂ))
      (H_wick H_real : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (V : Set (NPointDomain d n)) where
    U0 : Set (Fin n → Fin (d + 1) → ℂ)
    U0_open : IsOpen U0
    U0_connected : IsConnected U0
    wick_mem : ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U0 ∩ D_wick
    real_mem : ∀ x ∈ V, BHW.realEmbed x ∈ U0 ∩ D_real
    -- For every `x0 ∈ V`, a finite-dimensional affine complex chart supplies
    -- the positive wedge for the Wick branch and an opposite wedge contained
    -- in the real branch's holomorphic neighborhood.  The real branch itself
    -- may be defined on a full extended-tube neighborhood, not only on the
    -- opposite wedge.
    local_tube_chart :
      ∀ x0 ∈ V,
        ∃ (m : ℕ) (C : Set (Fin m → ℝ))
           (chart :
             (Fin n → Fin (d + 1) → ℂ) → (Fin m → ℂ))
           (unchart :
             (Fin m → ℂ) → (Fin n → Fin (d + 1) → ℂ))
           (P : Set (Fin n → Fin (d + 1) → ℂ))
           (E : Set (Fin m → ℝ))
           (bv : (Fin m → ℝ) → ℂ),
           IsOpen P ∧ BHW.realEmbed x0 ∈ P ∧
           IsOpen E ∧
           IsConnected E ∧
           E.Nonempty ∧
           (∃ y0 ∈ E, unchart (SCV.realEmbed y0) = BHW.realEmbed x0) ∧
           DifferentiableOn ℂ chart P ∧
           Continuous unchart ∧
           DifferentiableOn ℂ unchart (SCV.TubeDomain C) ∧
           DifferentiableOn ℂ unchart (SCV.TubeDomain (Neg.neg '' C)) ∧
           (∀ z ∈ P, unchart (chart z) = z) ∧
           (∀ u, unchart u ∈ P → chart (unchart u) = u) ∧
           (∀ y ∈ E, unchart (SCV.realEmbed y) ∈ P ∩ U0 ∩ D_real) ∧
           IsOpen C ∧ Convex ℝ C ∧ C.Nonempty ∧
           (0 : Fin m → ℝ) ∉ C ∧
           (∀ t y, 0 < t → y ∈ C → t • y ∈ C) ∧
           (∀ u ∈ SCV.TubeDomain C, unchart u ∈ P ∩ D_wick) ∧
           (∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
              unchart u ∈ P ∩ D_real) ∧
           (∀ z ∈ P ∩ D_wick, chart z ∈ SCV.TubeDomain C) ∧
           ContinuousOn bv E ∧
           (∀ y ∈ E,
              bv y = H_real (unchart (SCV.realEmbed y))) ∧
           (∀ y ∈ E,
              Filter.Tendsto
                (fun u => H_wick (unchart u))
                (nhdsWithin (SCV.realEmbed y) (SCV.TubeDomain C))
                (nhds (bv y))) ∧
           (∀ y ∈ E,
              Filter.Tendsto
                (fun u => H_real (unchart u))
                (nhdsWithin (SCV.realEmbed y)
                  (SCV.TubeDomain (Neg.neg '' C)))
                (nhds (bv y)))

  theorem SCV.differenceEnvelope_of_localBoundaryCharts
      (D_wick D_real : Set (Fin n → Fin (d + 1) → ℂ))
      (H_wick H_real : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (V : Set (NPointDomain d n))
      (hV_open : IsOpen V)
      (hV_connected : IsConnected V)
      (Data :
        SCV.LocalDifferenceEOWChartData D_wick D_real H_wick H_real V)
      (hH_wick : DifferentiableOn ℂ H_wick D_wick)
      (hH_real : DifferentiableOn ℂ H_real D_real) :
      ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
        (H : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        IsOpen U ∧ IsConnected U ∧
        DifferentiableOn ℂ H U ∧
        (∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U) ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
        (∀ x ∈ V,
          H (fun k => wickRotatePoint (x k)) =
            H_wick (fun k => wickRotatePoint (x k))) ∧
        (∀ x ∈ V,
          H (BHW.realEmbed x) = H_real (BHW.realEmbed x))

  theorem SCV.eow_differenceEnvelope_of_boundaryData_and_wickZero
      (D_wick D_real : Set (Fin n → Fin (d + 1) → ℂ))
      (H_wick H_real : (Fin n → Fin (d + 1) → ℂ) → ℂ)
      (V : Set (NPointDomain d n))
      (hV_open : IsOpen V)
      (hV_connected : IsConnected V)
      (Data :
        SCV.LocalDifferenceEOWChartData D_wick D_real H_wick H_real V)
      (hH_wick : DifferentiableOn ℂ H_wick D_wick)
      (hH_real : DifferentiableOn ℂ H_real D_real)
      (hWickZero :
        ∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
          ∫ x : NPointDomain d n,
            H_wick (fun k => wickRotatePoint (x k)) * φ x = 0) :
      ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
        (H : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        IsOpen U ∧ IsConnected U ∧
        DifferentiableOn ℂ H U ∧
        (∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U) ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
        (∀ x ∈ V,
          H (fun k => wickRotatePoint (x k)) =
            H_wick (fun k => wickRotatePoint (x k))) ∧
        (∀ x ∈ V,
          H (BHW.realEmbed x) = H_real (BHW.realEmbed x)) ∧
        (∀ x ∈ V, H (BHW.realEmbed x) = 0)
  ```

  Proof transcript for `SCV.differenceEnvelope_of_localBoundaryCharts`:

  1. For each `x0 ∈ V`, unpack `Data.local_tube_chart x0 hx0`.
  2. In chart coordinates, set
     `h_plus u := H_wick (unchart u)` on `SCV.TubeDomain C` and
     `h_minus u := H_real (unchart u)` on
     `SCV.TubeDomain (Neg.neg '' C)`.
  3. Holomorphy of `h_plus` and `h_minus` follows from `hH_wick`,
     `hH_real`, the positive/negative tube-to-domain fields, and
     differentiability of `unchart`.  This is why the data packet has both
     `∀ u ∈ TubeDomain C, unchart u ∈ P ∩ D_wick` and
     `∀ u ∈ TubeDomain (-C), unchart u ∈ P ∩ D_real`; the one-way field
     `z ∈ P ∩ D_wick -> chart z ∈ TubeDomain C` is needed later for agreement
     on Wick-domain points, but it is not enough to prove holomorphy of
     `H_wick ∘ unchart` on the whole tube.
  4. The two boundary-value hypotheses in `LocalDifferenceEOWChartData` give a
     common continuous boundary value `bv` on `E`.
  5. Apply `SCV.edge_of_the_wedge_theorem_connected_of_connected_edge` in these
     chart coordinates, using the `IsConnected E` field from
     `Data.local_tube_chart`, to obtain a connected local holomorphic extension
     `H_x0_chart` and the edge-value identity
     `H_x0_chart (SCV.realEmbed y) = bv y` for `y ∈ E`.
  6. Pull `H_x0_chart` back by `chart` to a local original-coordinate extension
     `H_x0` on `P ∩ U0`.  The inverse fields for `chart`/`unchart` prove its
     agreement with `H_wick` on the Wick wedge and with `H_real` on the real
     opposite wedge.  The real-edge trace follows from the EOW edge-value
     identity and the data field
     `bv y = H_real (unchart (SCV.realEmbed y))`.
  7. On overlaps of two local patches, the pulled-back extensions agree by the
     uniqueness clause in `SCV.edge_of_the_wedge_theorem` or by the ordinary
     identity theorem on the shared Wick wedge.  This is why `Data.U0_connected`
     is part of the packet.
  8. Glue in two layers.  First include the Wick-side domain piece
     `U_wick := U0 ∩ D_wick` with function `H_wick`; this is what contains the
     Wick-section points by `Data.wick_mem`.  Each local EOW patch overlaps this
     Wick piece on the image of `U_chart ∩ TubeDomain C`, because the data field
     `TubeDomain C -> P ∩ D_wick` puts the pulled-back positive wedge inside
     `D_wick` and the EOW agreement clause identifies the patch value with
     `H_wick` there.  Then glue the EOW patches to the Wick piece and to each
     other by the uniqueness/identity theorem.
  9. Take the connected component of this glued open union that contains the
     connected Wick-section image of `V`.  Every real-edge point
     `BHW.realEmbed x`, `x ∈ V`, lies in that same component because the local
     EOW patch at `x` contains the real edge point and a nonempty positive-tube
     overlap with the Wick component.  This gives the promised connected `U`
     containing both `{wick x | x ∈ V}` and `{realEmbed x | x ∈ V}`.
  10. The existing `SCV.edge_of_the_wedge_theorem` returns an open extension
     domain but does not expose connectedness.  Implementation should therefore
     add a small SCV strengthening, for example
     `SCV.edge_of_the_wedge_theorem_connected_of_connected_edge`, proved by
     the same polydisc construction plus the connected-edge argument above,
     rather than weakening the downstream identity theorem.

  Lean-facing statement for that SCV strengthening:

  ```lean
  theorem SCV.edge_of_the_wedge_theorem_connected_of_connected_edge {m : ℕ}
      (C : Set (Fin m → ℝ))
      (hC : IsOpen C) (hconv : Convex ℝ C)
      (h0 : (0 : Fin m → ℝ) ∉ C)
      (hcone : ∀ (t : ℝ) (y : Fin m → ℝ), 0 < t → y ∈ C → t • y ∈ C)
      (hCne : C.Nonempty)
      (f_plus f_minus : (Fin m → ℂ) → ℂ)
      (hf_plus : DifferentiableOn ℂ f_plus (SCV.TubeDomain C))
      (hf_minus :
        DifferentiableOn ℂ f_minus (SCV.TubeDomain (Neg.neg '' C)))
      (E : Set (Fin m → ℝ))
      (hE_open : IsOpen E)
      (hE_connected : IsConnected E)
      (bv : (Fin m → ℝ) → ℂ)
      (hbv_cont : ContinuousOn bv E)
      (hf_plus_bv : ∀ x ∈ E,
        Filter.Tendsto f_plus
          (nhdsWithin (SCV.realEmbed x) (SCV.TubeDomain C))
          (nhds (bv x)))
      (hf_minus_bv : ∀ x ∈ E,
        Filter.Tendsto f_minus
          (nhdsWithin (SCV.realEmbed x) (SCV.TubeDomain (Neg.neg '' C)))
          (nhds (bv x))) :
      ∃ (U : Set (Fin m → ℂ)) (F : (Fin m → ℂ) → ℂ),
        IsOpen U ∧ IsConnected U ∧
        (∀ x ∈ E, SCV.realEmbed x ∈ U) ∧
        DifferentiableOn ℂ F U ∧
        (∀ x ∈ E, F (SCV.realEmbed x) = bv x) ∧
        (∀ z ∈ U ∩ SCV.TubeDomain C, F z = f_plus z) ∧
        (∀ z ∈ U ∩ SCV.TubeDomain (Neg.neg '' C), F z = f_minus z) ∧
        (∀ (G : (Fin m → ℂ) → ℂ), DifferentiableOn ℂ G U →
          (∀ z ∈ U ∩ SCV.TubeDomain C, G z = f_plus z) →
          ∀ z ∈ U, G z = F z)
  ```

  Proof transcript:

  1. Reuse the exact `P_loc`, `F_loc`, `U := ⋃ x ∈ E, P_loc x`, and `F`
     construction from the proved `SCV.edge_of_the_wedge_theorem`; do not
     reprove the Cauchy-integral estimates or introduce a parallel EOW
     construction.
  2. The existing proof already has, for each `x ∈ E`, `IsOpen (P_loc x)`,
     `Convex ℝ (P_loc x)`, and `SCV.realEmbed x ∈ P_loc x`.  Hence every
     `P_loc x` is connected, and it meets the connected real-edge image
     `SCV.realEmbed '' E`.
  3. Prove `IsConnected U` by the standard union lemma: `SCV.realEmbed '' E` is
     connected by continuity of `SCV.realEmbed` and `hE_connected`; it is
     contained in `U`; each connected patch `P_loc x` intersects this common
     connected subset at `SCV.realEmbed x`; therefore the union of all patches
     over `E` is connected.  This is an extra wrapper around the existing proof,
     not a new analytic theorem.
  4. Keep the existing definition of `F` by choosing a local patch.  The
     independence of the chosen patch, holomorphy of `F`, the two tube
     agreement clauses, and the uniqueness clause are inherited verbatim from
     `SCV.edge_of_the_wedge_theorem`.
  5. Add the edge-value field
     `∀ x ∈ E, F (SCV.realEmbed x) = bv x` as follows.  From `F` holomorphic on
     the open set `U`, get continuity of `F` at `SCV.realEmbed x`.  Since
     `SCV.realEmbed x ∈ U` and `U` is open, the filter
     `nhdsWithin (SCV.realEmbed x) (SCV.TubeDomain C)` is eventually inside
     `U ∩ SCV.TubeDomain C`; on that filter `F = f_plus`.  The hypothesis
     `hf_plus_bv` gives convergence to `bv x`, while continuity gives
     convergence to `F (SCV.realEmbed x)`.  Uniqueness of limits in `ℂ` gives
     the desired equality.  The same proof could use the negative side, but one
     side is enough.
  6. The only new exported fields are `IsConnected U` and the real-edge value
     identity.  All analytic agreement and uniqueness content remains the
     already-proved EOW theorem, so this strengthening should be a short
     companion theorem in `SCV/TubeDomainExtension.lean`, not a new axiom.

  Proof transcript for `SCV.eow_differenceEnvelope_of_boundaryData_and_wickZero`
  after `SCV.differenceEnvelope_of_localBoundaryCharts` is available:

  1. Apply `SCV.differenceEnvelope_of_localBoundaryCharts` with `hV_open` and
     `hV_connected` to obtain `U`, `H`, holomorphy, Wick-edge trace, and
     real-edge trace.
  2. Apply
     `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` to
     `H` and the zero function on `U`, using `hWickZero` rewritten by the
     Wick-trace field, `hV_open`, and `hV_connected.1` for nonemptiness.  This
     gives `H = 0` on `U`.
  3. Evaluate at `BHW.realEmbed x` for `x ∈ V` and rewrite by the real-trace
     field to obtain `H_real (BHW.realEmbed x) = 0`.

  For the concrete OS §4.5 adjacent branch, do not leave `D_wick`,
  `D_real`, `H_wick`, and `H_real` abstract.  They should be the following
  definitions:

  ```lean
  def OS45AdjacentWickDifferenceDomain
      (i : Fin n) (hi : i.val + 1 < n)
      (ρ : Equiv.Perm (Fin n)) :
      Set (Fin n → Fin (d + 1) → ℂ) :=
    OS45WickChartDomain (d := d) (n := n) 1 ρ ∩
    OS45WickChartDomain (d := d) (n := n)
      (Equiv.swap i ⟨i.val + 1, hi⟩)
      ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)

  def OS45AdjacentRealDifferenceDomain
      (i : Fin n) (hi : i.val + 1 < n) :
      Set (Fin n → Fin (d + 1) → ℂ) :=
    OS45RealChartDomain (d := d) (n := n) 1 ∩
    OS45RealChartDomain (d := d) (n := n)
      (Equiv.swap i ⟨i.val + 1, hi⟩)

  def OS45AdjacentWickDifference
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (ρ : Equiv.Perm (Fin n)) :
      (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      OS45WickChart (d := d) OS lgc n
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ) z -
      OS45WickChart (d := d) OS lgc n 1 ρ z

  def OS45AdjacentRealDifference
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
      (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      OS45RealChart (d := d) OS lgc n
        (Equiv.swap i ⟨i.val + 1, hi⟩) z -
      OS45RealChart (d := d) OS lgc n 1 z
  ```

  The concrete OS45 data theorem should then be:

  ```lean
  theorem os45_adjacent_localDifferenceEOWChartData
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (V : Set (NPointDomain d n))
      (ρ : Equiv.Perm (Fin n))
      (hV_open : IsOpen V)
      (hV_nonempty : V.Nonempty)
      (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
      (hV_ordered : ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
      (hV_swap_ordered : ∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
      (hV_ET : ∀ x ∈ V,
        BHW.realEmbed x ∈ BHW.ExtendedTube d n)
      (hV_swapET : ∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n) :
      SCV.LocalDifferenceEOWChartData
        (OS45AdjacentWickDifferenceDomain (d := d) (n := n) i hi ρ)
        (OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi)
        (OS45AdjacentWickDifference (d := d) OS lgc n i hi ρ)
        (OS45AdjacentRealDifference (d := d) OS lgc n i hi)
        V
  ```

  Proof transcript for `os45_adjacent_localDifferenceEOWChartData`:

  1. Use `U0 := Set.univ` for the ambient chart packet.  This is not the final
     glued envelope and not a weak `U = Set.univ` shortcut: `U0` is only the
     harmless ambient set in which local EOW charts are expressed.  The actual
     connected holomorphic envelope is produced later by
     `SCV.differenceEnvelope_of_localBoundaryCharts`.
  2. `wick_mem` is exactly `hV_ordered` and `hV_swap_ordered`, transported by
     `wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector` and the
     definitions of the two `OS45WickChartDomain`s.
  3. `real_mem` is exactly `hV_ET` and `hV_swapET`, transported through
     `OS45RealChartDomain` and `BHW.permAct`.
  4. Holomorphy of `OS45AdjacentWickDifference` on
     `OS45AdjacentWickDifferenceDomain` is subtraction of the two
     `bvt_F_holomorphic` compositions.
  5. Holomorphy of `OS45AdjacentRealDifference` on
     `OS45AdjacentRealDifferenceDomain` is subtraction of the two
     `BHW.extendF_holomorphicOn` compositions, using
     `bvt_F_complexLorentzInvariant_forwardTube`.
  6. For each `x0 ∈ V`, the local chart and common boundary-value fields are
     the exact OS I §4.5 adjacent EOW/BHW claim: the two branch differences
     have the same boundary value on the real edge in a chart where the
     Wick-side branch occupies the positive wedge and the real branch contains
     an opposite wedge.  The chart is recorded as local `chart`/`unchart` data,
     not as a global linear map through the origin, because the EOW edge may be
     centered at an arbitrary real Jost point.  The hypothesis `hV_jost` is
     consumed here by the local BHW/Jost geometry theorem; ET and swapped-ET
     membership alone do not assert the real point is in the Jost edge.  The
     chart edge `E` should be chosen as a small connected real ball.  This is
     the remaining genuine
     analytic theorem; it should be proved or cited as a BHW/Jost-style local
     theorem with the fields above, not hidden as a generic geometry-only
     adapter.

  To make that last item implementation-ready, isolate the per-point theorem
  that fills exactly one `local_tube_chart` field:

  ```lean
  theorem os45_adjacent_local_tube_chart_with_commonBoundary
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (V : Set (NPointDomain d n))
      (ρ : Equiv.Perm (Fin n))
      (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
      (hV_ordered : ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
      (hV_swap_ordered : ∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
      (hV_ET : ∀ x ∈ V,
        BHW.realEmbed x ∈ BHW.ExtendedTube d n)
      (hV_swapET : ∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
      (x0 : NPointDomain d n) (hx0 : x0 ∈ V) :
      ∃ (m : ℕ) (C : Set (Fin m → ℝ))
         (chart :
           (Fin n → Fin (d + 1) → ℂ) → (Fin m → ℂ))
         (unchart :
           (Fin m → ℂ) → (Fin n → Fin (d + 1) → ℂ))
         (P : Set (Fin n → Fin (d + 1) → ℂ))
         (E : Set (Fin m → ℝ))
         (bv : (Fin m → ℝ) → ℂ),
         -- exactly the conjunction required by
         -- `SCV.LocalDifferenceEOWChartData.local_tube_chart` for
         -- `D_wick = OS45AdjacentWickDifferenceDomain i hi ρ`,
         -- `D_real = OS45AdjacentRealDifferenceDomain i hi`,
         -- `H_wick = OS45AdjacentWickDifference OS lgc n i hi ρ`, and
         -- `H_real = OS45AdjacentRealDifference OS lgc n i hi`.
         IsOpen P ∧ BHW.realEmbed x0 ∈ P ∧
         IsOpen E ∧ IsConnected E ∧ E.Nonempty ∧
         (∃ y0 ∈ E, unchart (SCV.realEmbed y0) = BHW.realEmbed x0) ∧
         DifferentiableOn ℂ chart P ∧
         Continuous unchart ∧
         DifferentiableOn ℂ unchart (SCV.TubeDomain C) ∧
         DifferentiableOn ℂ unchart (SCV.TubeDomain (Neg.neg '' C)) ∧
         (∀ z ∈ P, unchart (chart z) = z) ∧
         (∀ u, unchart u ∈ P → chart (unchart u) = u) ∧
         (∀ y ∈ E,
            unchart (SCV.realEmbed y) ∈ P ∩
              OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi) ∧
         IsOpen C ∧ Convex ℝ C ∧ C.Nonempty ∧
         (0 : Fin m → ℝ) ∉ C ∧
         (∀ t y, 0 < t → y ∈ C → t • y ∈ C) ∧
         (∀ u ∈ SCV.TubeDomain C,
            unchart u ∈ P ∩
              OS45AdjacentWickDifferenceDomain (d := d) (n := n) i hi ρ) ∧
         (∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
            unchart u ∈ P ∩
              OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi) ∧
         (∀ z ∈ P ∩
            OS45AdjacentWickDifferenceDomain (d := d) (n := n) i hi ρ,
            chart z ∈ SCV.TubeDomain C) ∧
         ContinuousOn bv E ∧
         (∀ y ∈ E,
            bv y =
              OS45AdjacentRealDifference (d := d) OS lgc n i hi
                (unchart (SCV.realEmbed y))) ∧
         (∀ y ∈ E,
            Filter.Tendsto
              (fun u =>
                OS45AdjacentWickDifference (d := d) OS lgc n i hi ρ
                  (unchart u))
              (nhdsWithin (SCV.realEmbed y) (SCV.TubeDomain C))
              (nhds (bv y))) ∧
         (∀ y ∈ E,
            Filter.Tendsto
              (fun u =>
                OS45AdjacentRealDifference (d := d) OS lgc n i hi
                  (unchart u))
              (nhdsWithin (SCV.realEmbed y)
                (SCV.TubeDomain (Neg.neg '' C)))
              (nhds (bv y)))
  ```

  Proof transcript for `os45_adjacent_local_tube_chart_with_commonBoundary`:

  1. Set `τ := Equiv.swap i ⟨i.val + 1, hi⟩` and
     `ρτ := τ.symm * ρ`.  The two Wick branches are
     `OS45WickChart 1 ρ` and `OS45WickChart τ ρτ`; the two real branches are
     `OS45RealChart 1` and `OS45RealChart τ`.
  2. Use `hV_ordered x0 hx0` and `hV_swap_ordered x0 hx0`, via
     `wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector`, to place
     the two Wick charts in the correct permuted forward-tube source domains.
     Use `hV_ET x0 hx0` and `hV_swapET x0 hx0` to place the two real charts in
     the two extended-tube source domains.
  3. Apply the local BHW/Jost geometry theorem at the adjacent real Jost point
     `BHW.realEmbed x0`, using `hV_jost x0 hx0` as the Jost-edge hypothesis.
     The theorem supplies a finite-dimensional affine chart centered at this
     point, a connected real edge ball `E`, and an open cone `C` with four
     distinct direction fields:
     positive-tube points map into `P ∩` the adjacent Wick difference domain,
     negative-tube points map into `P ∩` the adjacent real difference domain,
     real edge points map into the real difference domain, and Wick-domain
     points in the local patch map back into `TubeDomain C`.  This theorem is
     pure BHW/SCV geometry; it should mention only the relevant tube domains and
     adjacent Jost/ET hypotheses, not OS fields.
  4. Apply the branchwise OS §4.5/BHW-Jost boundary theorem
     `os45_singleBranch_commonBoundaryValue_from_localEOWGeometry` to the
     identity branch `(σ, ρσ) = (1, ρ)` and to the adjacent branch
     `(σ, ρσ) = (τ, ρτ)`.  This produces boundary values `bv_id` and `bv_τ`
     equal to the corresponding real `extendF` traces on the real edge.  The
     Wick-side Tendsto clauses are part of this branchwise theorem; they must
     not be replaced by a bare `BHW.extendF_eq_on_forwardTube`, because the
     permuted branch argument need not lie in the ordinary forward tube.
  5. Define the branch-difference boundary value by
     `bv y := bv_τ y - bv_id y`.  Continuity follows from continuity of the two
     branch boundary values.  The two Tendsto clauses are obtained by
     subtracting the branchwise Tendsto statements.
  6. The theorem never proves or uses
     `OS45WickChart σ ρσ (wick x) = OS45RealChart σ (realEmbed x)` for a
     single branch.  It only identifies the common boundary values of the two
     analytic continuations in the local EOW chart, and then subtracts.

  The two sublemmas that make the per-point theorem implementation-ready are
  the following.  First isolate the geometry, with no `OS` or `lgc` parameters:

  ```lean
  theorem os45_adjacent_localEOWGeometry
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (V : Set (NPointDomain d n))
      (ρ : Equiv.Perm (Fin n))
      (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
      (hV_ordered : ∀ x ∈ V,
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
      (hV_swap_ordered : ∀ x ∈ V,
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ))
      (hV_ET : ∀ x ∈ V,
        BHW.realEmbed x ∈ BHW.ExtendedTube d n)
      (hV_swapET : ∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
      (x0 : NPointDomain d n) (hx0 : x0 ∈ V) :
      ∃ (m : ℕ) (C : Set (Fin m → ℝ))
         (chart :
           (Fin n → Fin (d + 1) → ℂ) → (Fin m → ℂ))
         (unchart :
           (Fin m → ℂ) → (Fin n → Fin (d + 1) → ℂ))
         (P : Set (Fin n → Fin (d + 1) → ℂ))
         (E : Set (Fin m → ℝ)),
         IsOpen P ∧ BHW.realEmbed x0 ∈ P ∧
         IsOpen E ∧ IsConnected E ∧ E.Nonempty ∧
         (∃ y0 ∈ E, unchart (SCV.realEmbed y0) = BHW.realEmbed x0) ∧
         DifferentiableOn ℂ chart P ∧
         Continuous unchart ∧
         DifferentiableOn ℂ unchart (SCV.TubeDomain C) ∧
         DifferentiableOn ℂ unchart (SCV.TubeDomain (Neg.neg '' C)) ∧
         (∀ z ∈ P, unchart (chart z) = z) ∧
         (∀ u, unchart u ∈ P → chart (unchart u) = u) ∧
         (∀ y ∈ E,
            unchart (SCV.realEmbed y) ∈ P ∩
              OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi) ∧
         IsOpen C ∧ Convex ℝ C ∧ C.Nonempty ∧
         (0 : Fin m → ℝ) ∉ C ∧
         (∀ t y, 0 < t → y ∈ C → t • y ∈ C) ∧
         (∀ u ∈ SCV.TubeDomain C,
            unchart u ∈ P ∩
              OS45AdjacentWickDifferenceDomain (d := d) (n := n) i hi ρ) ∧
         (∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
            unchart u ∈ P ∩
              OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi) ∧
         (∀ z ∈ P ∩
            OS45AdjacentWickDifferenceDomain (d := d) (n := n) i hi ρ,
            chart z ∈ SCV.TubeDomain C)
  ```

  Proof transcript for `os45_adjacent_localEOWGeometry`:

  1. Set `τ := Equiv.swap i ⟨i.val + 1, hi⟩` and `ρτ := τ.symm * ρ`.
  2. Use the ordered-sector hypotheses only to prove that the Wick-rotated
     `ρ`-ordered and `ρτ`-ordered configurations are in `ForwardTube d n`.
     This supplies the positive-tube direction field for the two Wick chart
     domains; do not assert that the raw swapped Wick configuration is itself in
     the ordinary forward tube.
  3. Use `hV_ET` and `hV_swapET` only for the real branch domain.  Since
     `BHW.ExtendedTube d n` is open and stable under the local BHW/Jost
     opposite-wedge construction, and since `hV_jost x0 hx0` supplies the real
     Jost-edge base point, choose a small connected real edge ball `E` around
     the chart coordinate of `BHW.realEmbed x0` whose real image remains inside
     both real chart domains and inside the real edge patch required by the
     local BHW/Jost theorem.
  4. The previously preferred affine single-chart supplier
     `BHW.localAdjacentOS45OppositeWedgeChart_at_jostSeed` has been retracted:
     its full-dimensional orbit-witness fields were too strong.  A corrected
     chart route may still choose a local wedge over the adjacent real edge,
     but the chart theorem must identify branch differences through common
     analytic continuation / PET-Jost boundary transfer.  It must not assert
     that an adjacent point swap is implemented by a Lorentz transformation on
     a generic full-dimensional tube.
  5. Use an affine chart whose inverse identities hold on `P`; in the simplest
     implementation `P` may be `Set.univ`, but it must at least contain the
     positive and negative tube images required by the two tube-to-domain fields.
     The fields `pos_tube -> P ∩ D_wick` and `neg_tube -> P ∩ D_real` are what
     make the later EOW-to-Wick gluing honest.

  **Retraction.**  The branchwise local-boundary theorem surfaces in the rest
  of this subsection are not active, because they depend on the same false
  `hposOrbit` idea.  The OS §4.5 boundary-value step must be rewritten as a
  branch-difference theorem using common analytic continuation / PET-Jost
  boundary transfer, not as a pair of single-branch `extendF` continuity
  theorems from local orbit witnesses.

  The older, now-retracted branchwise theorem surface was:

  ```lean
  theorem os45_singleBranch_commonBoundaryValue_from_localEOWGeometry
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ)
      (σ ρσ : Equiv.Perm (Fin n))
      (m : ℕ) (C : Set (Fin m → ℝ))
      (unchart :
        (Fin m → ℂ) → (Fin n → Fin (d + 1) → ℂ))
      (E : Set (Fin m → ℝ))
      (hE_open : IsOpen E)
      (hE_to_real :
        ∀ y ∈ E,
          unchart (SCV.realEmbed y) ∈
            OS45RealChartDomain (d := d) (n := n) σ)
      (hunchart_cont : Continuous unchart)
      (hpos :
        ∀ u ∈ SCV.TubeDomain C,
          unchart u ∈
            OS45WickChartDomain (d := d) (n := n) σ ρσ)
      (hneg :
        ∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
          unchart u ∈
            OS45RealChartDomain (d := d) (n := n) σ)
      (hposOrbit :
        ∀ u ∈ SCV.TubeDomain C,
          ∃ Λ : ComplexLorentzGroup d,
            BHW.permAct (d := d) σ (unchart u) =
              BHW.complexLorentzAction Λ
                (BHW.permAct (d := d) ρσ
                  (BHW.permAct (d := d) σ (unchart u)))) :
      ∃ bvσ : (Fin m → ℝ) → ℂ,
        ContinuousOn bvσ E ∧
        (∀ y ∈ E,
          bvσ y =
            OS45RealChart (d := d) OS lgc n σ
              (unchart (SCV.realEmbed y))) ∧
        (∀ y ∈ E,
          Filter.Tendsto
            (fun u =>
              OS45WickChart (d := d) OS lgc n σ ρσ (unchart u))
            (nhdsWithin (SCV.realEmbed y) (SCV.TubeDomain C))
            (nhds (bvσ y))) ∧
        (∀ y ∈ E,
          Filter.Tendsto
            (fun u =>
              OS45RealChart (d := d) OS lgc n σ (unchart u))
            (nhdsWithin (SCV.realEmbed y)
              (SCV.TubeDomain (Neg.neg '' C)))
            (nhds (bvσ y)))
  ```

  Proof transcript for
  `os45_singleBranch_commonBoundaryValue_from_localEOWGeometry`:

  1. Define
     `bvσ y := OS45RealChart OS lgc n σ (unchart (SCV.realEmbed y))`.
  2. Continuity of `bvσ` follows from `hunchart_cont`, `hE_to_real`, and
     `BHW.extendF_holomorphicOn` for the selected witness.
  3. The negative-wedge Tendsto is ordinary continuity of
     `OS45RealChart σ ∘ unchart` on the real chart domain, using `hneg` and
     `hE_to_real`.
  4. The positive-wedge Tendsto is the standard local BHW/Jost boundary
     compatibility between the permuted forward-tube branch
     `OS45WickChart σ ρσ` and the `extendF` branch `OS45RealChart σ`.
     It consumes the selected witness holomorphy,
     `bvt_F_complexLorentzInvariant_forwardTube`, `hpos`, `hposOrbit`, and
     the local BHW chart geometry.  Do not replace this step by a bare
     `BHW.extendF_eq_on_forwardTube`: for a permuted branch, the argument of
     `extendF` need not lie in the ordinary forward tube.

  Circularity firewall for this branchwise theorem:

  - Do **not** cite `W_analytic_swap_boundary_pairing_eq`,
    `analytic_extended_local_commutativity`,
    `BHW.extendF_adjSwap_eq_on_realOpen_of_distributional_local_commutativity`,
    or any theorem whose hypotheses include `IsLocallyCommutativeWeak d W`.
    Those results are downstream of locality and are therefore circular for
    theorem 2.
  - Do **not** use `extendF_adjSwap_eq_on_realOpen`,
    `extendF_adjSwap_eq_of_connected_overlap`, or the selected-edge-data
    consumer to prove this theorem.  Those are exactly the theorems the OS45
    packet is meant to supply.
  - The allowed inputs are OS-internal and external analytic inputs only:
    `bvt_F_holomorphic`, `bvt_F_perm` only for harmless Wick-section
    normalization, the selected boundary-value/growth package for `bvt_F`,
    `bvt_F_complexLorentzInvariant_forwardTube`, and the non-circular local
    BHW/Jost orbit theorem.

  Lean-facing proof of the positive-wedge Tendsto should be organized as
  follows, so the circularity is visible in the code:

  1. For fixed `y ∈ E`, set `z₀ := unchart (SCV.realEmbed y)`.  From
     `hE_to_real`, obtain
     `BHW.permAct σ z₀ ∈ BHW.ExtendedTube d n`; this only identifies the
     real branch domain of `OS45RealChart σ`.
  2. For `u → SCV.realEmbed y` inside `SCV.TubeDomain C`, use `hpos` to know
     `BHW.permAct ρσ (BHW.permAct σ (unchart u)) ∈ ForwardTube d n`.  Thus
     the positive-side branch is the selected forward-tube function
     `bvt_F OS lgc n` evaluated on an honest forward-tube point.
  3. The local BHW/Jost theorem supplies a complex-Lorentz/Jost continuation
     bridge from those positive-side forward-tube points to the real
     extended-tube branch `BHW.extendF (bvt_F OS lgc n) (BHW.permAct σ z₀)`.
     The proof of this bridge uses OS §4.5 equations `(4.12)` and `(4.14)`:
     `(4.12)` gives the selected Fourier-Laplace analytic function and
     `(4.14)` gives the Lorentz-covariance compatibility needed to pass along
     the complex-Lorentz orbit.  It does **not** use already-proved locality.
  4. The permutation `ρσ` is handled by the local orbit witness: the ordered
     point `BHW.permAct ρσ (BHW.permAct σ (unchart u))` is the actual
     forward-tube preimage used to evaluate the selected witness.  Do not claim
     `BHW.permAct σ (unchart u)` itself lies in the ordinary forward tube.  A
     `bvt_F_perm` rewrite is needed only later on the Wick section, where the
     identity
     `BHW.permAct (τ.symm * ρ) (BHW.permAct τ (wick x)) =
      BHW.permAct ρ (wick x)`
     normalizes the two adjacent Wick traces.
  5. The conclusion is exactly the Tendsto statement to
     `bvσ y = OS45RealChart OS lgc n σ z₀`.  No pointwise equality between a
     Wick-section value and a real-section value is produced.

  The positive-wedge boundary step should be implemented through a local
  orbit-to-`extendF` bridge, not as a black-box continuity assertion for the
  total function `bvt_F`.  The Lean-facing helper is:

  ```lean
  theorem os45_singleBranch_positiveTube_eq_extendF_from_localOrbit
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ)
      (σ ρσ : Equiv.Perm (Fin n))
      (m : ℕ) (C : Set (Fin m → ℝ))
      (unchart :
        (Fin m → ℂ) → (Fin n → Fin (d + 1) → ℂ))
      (hposFT :
        ∀ u ∈ SCV.TubeDomain C,
          BHW.permAct (d := d) ρσ
            (BHW.permAct (d := d) σ (unchart u)) ∈
            BHW.ForwardTube d n)
      (hposOrbit :
        ∀ u ∈ SCV.TubeDomain C,
          ∃ Λ : ComplexLorentzGroup d,
            BHW.permAct (d := d) σ (unchart u) =
              BHW.complexLorentzAction Λ
                (BHW.permAct (d := d) ρσ
                  (BHW.permAct (d := d) σ (unchart u)))) :
      ∀ u ∈ SCV.TubeDomain C,
        OS45WickChart (d := d) OS lgc n σ ρσ (unchart u) =
          OS45RealChart (d := d) OS lgc n σ (unchart u)
  ```

  Proof transcript:

  1. Set `F := bvt_F OS lgc n`,
     `w u := BHW.permAct ρσ (BHW.permAct σ (unchart u))`, and
     `z u := BHW.permAct σ (unchart u)`.
  2. Convert `bvt_F_complexLorentzInvariant_forwardTube` to the BHW
     `ForwardTube` convention using `BHW_forwardTube_eq`; call the resulting
     complex Lorentz invariance hypothesis `hF_cinv`.
  3. For fixed `u ∈ TubeDomain C`, obtain `Λ` from `hposOrbit u hu`.
     Together with `hposFT u hu`, this proves `z u ∈ BHW.ExtendedTube d n`
     and gives an explicit forward-tube preimage of `z u`.
  4. Unfold `OS45WickChart` and `OS45RealChart`.  The desired equality is
     exactly the defining equality for `BHW.extendF F (z u)` with preimage
     `w u`; prove it using `BHW.extendF_preimage_eq` or the local
     `extendF` preimage lemma already available in `BHWCore.lean`.
  5. This proof uses only selected-witness holomorphy/covariance and the local
     BHW orbit witness.  It does **not** use
     `extendF_perm_overlap_of_edgePairingEquality`,
     `bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`, or any theorem that
     assumes local commutativity.

  The actual positive-side Tendsto in
  `os45_singleBranch_commonBoundaryValue_from_localEOWGeometry` then follows
  from this helper plus continuity of `extendF` on `BHW.ExtendedTube`:

  ```lean
  theorem os45_singleBranch_positiveTendsto_from_localOrbit
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ)
      (σ ρσ : Equiv.Perm (Fin n))
      (m : ℕ) (C : Set (Fin m → ℝ))
      (unchart :
        (Fin m → ℂ) → (Fin n → Fin (d + 1) → ℂ))
      (E : Set (Fin m → ℝ))
      (hunchart_cont : Continuous unchart)
      (hposFT :
        ∀ u ∈ SCV.TubeDomain C,
          BHW.permAct (d := d) ρσ
            (BHW.permAct (d := d) σ (unchart u)) ∈
            BHW.ForwardTube d n)
      (hposOrbit :
        ∀ u ∈ SCV.TubeDomain C,
          ∃ Λ : ComplexLorentzGroup d,
            BHW.permAct (d := d) σ (unchart u) =
              BHW.complexLorentzAction Λ
                (BHW.permAct (d := d) ρσ
                  (BHW.permAct (d := d) σ (unchart u))))
      (hrealET :
        ∀ y ∈ E,
          BHW.permAct (d := d) σ (unchart (SCV.realEmbed y)) ∈
            BHW.ExtendedTube d n) :
      ∀ y ∈ E,
        Filter.Tendsto
          (fun u =>
            OS45WickChart (d := d) OS lgc n σ ρσ (unchart u))
          (nhdsWithin (SCV.realEmbed y) (SCV.TubeDomain C))
          (nhds
            (OS45RealChart (d := d) OS lgc n σ
              (unchart (SCV.realEmbed y))))
  ```

  Proof transcript:

  1. Use `os45_singleBranch_positiveTube_eq_extendF_from_localOrbit` to
     replace the positive-side function by
     `u ↦ BHW.extendF (bvt_F OS lgc n) (BHW.permAct σ (unchart u))` on
     `SCV.TubeDomain C`.
  2. The map `u ↦ BHW.permAct σ (unchart u)` is continuous by
     `hunchart_cont` and continuity of finite coordinate permutation.
  3. The local orbit equality plus `hposFT` shows that this map sends the
     positive tube into `BHW.ExtendedTube d n`; `hrealET` gives the boundary
     point's membership.
  4. `BHW.extendF_holomorphicOn` applied to `bvt_F_holomorphic` and
     `bvt_F_complexLorentzInvariant_forwardTube` gives `ContinuousOn
     (BHW.extendF (bvt_F OS lgc n)) (BHW.ExtendedTube d n)`.
  5. Compose these continuities to get Tendsto to the real branch value.  This
     is the precise replacement for the previously vague phrase "BHW/Jost
     boundary compatibility".

  The corresponding negative-side Tendsto is even smaller:

  ```lean
  theorem os45_singleBranch_negativeTendsto_from_extendF_continuity
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ)
      (σ : Equiv.Perm (Fin n))
      (m : ℕ) (C : Set (Fin m → ℝ))
      (unchart :
        (Fin m → ℂ) → (Fin n → Fin (d + 1) → ℂ))
      (E : Set (Fin m → ℝ))
      (hunchart_cont : Continuous unchart)
      (hnegET :
        ∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
          BHW.permAct (d := d) σ (unchart u) ∈
            BHW.ExtendedTube d n)
      (hrealET :
        ∀ y ∈ E,
          BHW.permAct (d := d) σ (unchart (SCV.realEmbed y)) ∈
            BHW.ExtendedTube d n) :
      ∀ y ∈ E,
        Filter.Tendsto
          (fun u =>
            OS45RealChart (d := d) OS lgc n σ (unchart u))
          (nhdsWithin (SCV.realEmbed y)
            (SCV.TubeDomain (Neg.neg '' C)))
          (nhds
            (OS45RealChart (d := d) OS lgc n σ
              (unchart (SCV.realEmbed y))))
  ```

  Its proof is continuity of
  `BHW.extendF (bvt_F OS lgc n) ∘ BHW.permAct σ ∘ unchart` on the negative
  tube.  It needs no permutation symmetry input at all.

  The adjacent branch-difference boundary theorem is then obtained by applying
  the single-branch theorem twice and subtracting:

  ```lean
  theorem os45_adjacent_commonBoundaryValue_from_localEOWGeometry
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (ρ : Equiv.Perm (Fin n))
      (m : ℕ) (C : Set (Fin m → ℝ))
      (unchart :
        (Fin m → ℂ) → (Fin n → Fin (d + 1) → ℂ))
      (E : Set (Fin m → ℝ))
      (hE_open : IsOpen E)
      (hE_to_real :
        ∀ y ∈ E,
          unchart (SCV.realEmbed y) ∈
            OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi)
      (hunchart_cont : Continuous unchart)
      (hpos :
        ∀ u ∈ SCV.TubeDomain C,
          unchart u ∈
            OS45AdjacentWickDifferenceDomain (d := d) (n := n) i hi ρ)
      (hneg :
        ∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
          unchart u ∈
            OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi)
      (hposOrbit_id :
        ∀ u ∈ SCV.TubeDomain C,
          ∃ Λ : ComplexLorentzGroup d,
            BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
                (unchart u) =
              BHW.complexLorentzAction Λ
                (BHW.permAct (d := d) ρ
                  (BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
                    (unchart u))))
      (hposOrbit_swap :
        ∀ u ∈ SCV.TubeDomain C,
          ∃ Λ : ComplexLorentzGroup d,
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                (unchart u) =
              BHW.complexLorentzAction Λ
                (BHW.permAct (d := d)
                  ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
                  (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                    (unchart u)))) :
      ∃ bv : (Fin m → ℝ) → ℂ,
        ContinuousOn bv E ∧
        (∀ y ∈ E,
          bv y =
            OS45AdjacentRealDifference (d := d) OS lgc n i hi
              (unchart (SCV.realEmbed y))) ∧
        (∀ y ∈ E,
          Filter.Tendsto
            (fun u =>
              OS45AdjacentWickDifference (d := d) OS lgc n i hi ρ
                (unchart u))
            (nhdsWithin (SCV.realEmbed y) (SCV.TubeDomain C))
            (nhds (bv y))) ∧
        (∀ y ∈ E,
          Filter.Tendsto
            (fun u =>
              OS45AdjacentRealDifference (d := d) OS lgc n i hi
                (unchart u))
            (nhdsWithin (SCV.realEmbed y)
              (SCV.TubeDomain (Neg.neg '' C)))
            (nhds (bv y)))
  ```

  Proof transcript for
  `os45_adjacent_commonBoundaryValue_from_localEOWGeometry`:

  1. Set `τ := Equiv.swap i ⟨i.val + 1, hi⟩` and `ρτ := τ.symm * ρ`.
  2. From `hpos`, derive the two branchwise positive-domain fields for
     `(σ, ρσ) = (1, ρ)` and `(τ, ρτ)`.  From `hneg` and `hE_to_real`, derive
     the corresponding real-domain and real-edge fields.  Pass
     `hposOrbit_id` and `hposOrbit_swap` to the positive Tendsto helper.
  3. Apply `os45_singleBranch_commonBoundaryValue_from_localEOWGeometry` twice,
     obtaining `bv_id` and `bv_τ`.
  4. Define `bv y := bv_τ y - bv_id y`.  Continuity follows by subtraction, and
     the real-edge trace field unfolds to
     `OS45AdjacentRealDifference OS lgc n i hi (unchart (SCV.realEmbed y))`.
  5. Subtract the two branchwise Tendsto statements to get the final
     branch-difference Tendsto clauses.  This is a boundary-limit comparison at
     the real edge; it does not compare a Wick-section value with a real-section
     value at the same real configuration.

  This is still a theorem-shape target, not a new axiom request.  The missing
  theorem is the construction of `LocalDifferenceEOWChartData` for the concrete
  adjacent OS45 chart pair, from the ACR(1) / permuted-forward-tube /
  extended-tube geometry and the common real-edge boundary statement in OS I
  §4.5.  The pointwise EOW theorem is sufficient for this local chart packet
  because the boundary value is the continuous `extendF` real-edge trace, not a
  raw value of `bvt_F` at a real boundary point.  The compact-test/distributional
  input enters later, when
  `SCV.eow_differenceEnvelope_of_boundaryData_and_wickZero` uses the Wick-side
  zero pairing to force the already-constructed difference envelope to vanish.
  If a future route tries to bypass the `extendF` trace and use raw
  `bvt_F(realEmbed x)` values, that would require a separate distributional EOW
  theorem for **branch differences**, not a one-branch Wick-to-real equality.

  Implementation transcript for `os45_adjacent_branchDifferenceEnvelope_exists`:

  1. Set
     `D_wick := OS45AdjacentWickDifferenceDomain i hi ρ`,
     `D_real := OS45AdjacentRealDifferenceDomain i hi`,
     `H_wick := OS45AdjacentWickDifference OS lgc n i hi ρ`, and
     `H_real := OS45AdjacentRealDifference OS lgc n i hi`.
  2. Obtain

     ```lean
     Data :
       SCV.LocalDifferenceEOWChartData D_wick D_real H_wick H_real V
     ```

     from `os45_adjacent_localDifferenceEOWChartData` with the same
     `ρ`, `hV_jost`, `hV_ordered`, `hV_swap_ordered`, `hV_ET`, and
     `hV_swapET`.
     This theorem-level statement is the OS §4.5 local EOW/BHW analytic input;
     do not hide it as a field in another structure.
  3. Prove
     `DifferentiableOn ℂ H_wick D_wick` by subtracting the two
     `OS45WickChart` holomorphy lemmas, and prove
     `DifferentiableOn ℂ H_real D_real` by subtracting the two
     `OS45RealChart` holomorphy lemmas.
  4. Apply

     ```lean
     SCV.differenceEnvelope_of_localBoundaryCharts
       D_wick D_real H_wick H_real V hV_open hV_connected Data
       hH_wick hH_real
     ```

     and unpack the returned `U`, `H`, `U_open`, `U_connected`, `H_holo`,
     `wick_mem`, `real_mem`, `wick_trace`, and `real_trace`.
  5. Repackage those fields as the conclusion of
     `os45_adjacent_branchDifferenceEnvelope_exists`.  The two trace fields are
     definitional after unfolding `H_wick` and `H_real`; no single-branch
     Wick-to-real comparison is used.

  Production placement rule: if this reaches Lean before every proof is
  available, the only acceptable theorem-level `sorry`s are the standard SCV
  theorem `SCV.differenceEnvelope_of_localBoundaryCharts` and/or the concrete
  OS theorem `os45_adjacent_localDifferenceEOWChartData`.  Do not introduce a
  production structure with a `glued_envelope` field, and do not put `sorry` in
  any definition or structure field.

  Implementation refinement after the #1092 audit: the generic local-chart
  gluing theorem is mathematically honest, but it is broader than the current
  `2 ≤ d` edge supplier needs.  The selector already chooses `V` as a small
  connected ball around one adjacent real Jost point.  The preferred Lean route
  is therefore to choose that ball **inside one OS45 local EOW chart** and build
  the branch-difference envelope from a single application of the connected
  EOW theorem.  This avoids a large sheaf-gluing proof while preserving the
  same mathematical content.

  **Retraction after the #1104 orbit-invariant audit.**  The single-chart
  geometry shape below is no longer an implementation target.  It asked for a
  full-dimensional affine tube on which a nontrivial point permutation is
  realized by a complex Lorentz transformation at every point of the tube.
  That is generically false: complex Lorentz transformations preserve the
  labelled Minkowski Gram matrix of the spacetime vectors, while swapping two
  arbitrary point labels changes the labelled diagonal entries unless the two
  point norms happen to agree.  A full-dimensional tube necessarily contains
  configurations with unequal labelled quadratic forms.

  Therefore the code block below is retained only as a negative design record:
  do not implement it, do not reintroduce its `pos_orbit_id` /
  `pos_orbit_swap` fields, and do not use a theorem-level `sorry` to reserve
  this shape.  The production theorem
  `BHW.localAdjacentJostOppositeCone_at_seed` was removed from
  `OS45LocalOppositeWedge.lean` after this audit.  The proved helper lemmas in
  that file remain valid.

  The now-retracted Lean-facing shape was:

  ```lean
  structure OS45AdjacentSingleEOWGeometry
      (d n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n)) where
    V_open : IsOpen V
    V_connected : IsConnected V
    V_nonempty : V.Nonempty
    V_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n
    V_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n
    V_swapET : ∀ x ∈ V,
      BHW.realEmbed
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        BHW.ExtendedTube d n
    V_ordered : ∀ x ∈ V,
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ
    V_swap_ordered : ∀ x ∈ V,
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
    m : ℕ
    C : Set (Fin m → ℝ)
    center : Fin n → Fin (d + 1) → ℂ
    chartCLE :
      (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin m → ℂ)
    realChartCoord : NPointDomain d n → Fin m → ℝ
    realChartCoord_cont : Continuous realChartCoord
    E : Set (Fin m → ℝ)
    E_open : IsOpen E
    E_connected : IsConnected E
    E_nonempty : E.Nonempty
    C_open : IsOpen C
    C_convex : Convex ℝ C
    C_nonempty : C.Nonempty
    C_not_zero : (0 : Fin m → ℝ) ∉ C
    C_cone : ∀ t y, 0 < t → y ∈ C → t • y ∈ C
    wick_coord : ∀ x ∈ V,
      chartCLE ((fun k => wickRotatePoint (x k)) - center) ∈
        SCV.TubeDomain C
    real_coord_eq : ∀ x ∈ V,
      chartCLE (BHW.realEmbed x - center) =
        SCV.realEmbed (realChartCoord x)
    real_coord_mem : ∀ x ∈ V, realChartCoord x ∈ E
    pos_domain : ∀ u ∈ SCV.TubeDomain C,
      center + chartCLE.symm u ∈
        OS45AdjacentWickDifferenceDomain (d := d) (n := n) i hi ρ
    neg_domain : ∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
      center + chartCLE.symm u ∈
        OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi
    edge_domain : ∀ y ∈ E,
      center + chartCLE.symm (SCV.realEmbed y) ∈
        OS45AdjacentRealDifferenceDomain (d := d) (n := n) i hi
    pos_orbit_id : ∀ u ∈ SCV.TubeDomain C,
      ∃ Λ : ComplexLorentzGroup d,
        BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
            (center + chartCLE.symm u) =
          BHW.complexLorentzAction Λ
            (BHW.permAct (d := d) ρ
              (BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
                (center + chartCLE.symm u)))
    pos_orbit_swap : ∀ u ∈ SCV.TubeDomain C,
      ∃ Λ : ComplexLorentzGroup d,
        BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
            (center + chartCLE.symm u) =
          BHW.complexLorentzAction Λ
            (BHW.permAct (d := d)
              ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
              (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                (center + chartCLE.symm u)))
  ```

  The fatal point in this retracted shape is not the use of an affine chart or
  the connected real edge.  The fatal point is the full-dimensional
  `pos_orbit_*` requirement.  Point permutations act on the label set
  `Fin n`; Lorentz transformations act on the spacetime index
  `Fin (d + 1)`.  For a nontrivial adjacent swap, demanding
  `permAct τ z = Λ • z` on a full-dimensional open tube would force equality
  of the Lorentz-invariant labelled quadratic data of the two swapped point
  vectors throughout that tube.  This is not an open condition and fails for
  generic configurations.

  A correct OS §4.5 route must therefore avoid pointwise "permutation is a
  Lorentz orbit" witnesses on a full ambient tube.  The branch comparison has
  to be carried by the BHW/PET analytic continuation and Jost boundary theorem,
  or by a genuinely local edge-of-the-wedge chart whose domain is a local edge
  wedge and whose equality statement is a branch-difference boundary statement,
  not a full-tube Lorentz-orbit parametrization of point permutations.

  The previously vague phrase "apply the local BHW/Jost opposite-wedge
  theorem" still has to be replaced, but not by the retracted full-dimensional
  orbit statement.  The corrected replacement must be one of the following:

  1. a generic external BHW/PET branch-independence theorem for forward-tube
     holomorphic functions, independent of `OS` and `lgc`, followed by the OS
     §4.5 boundary-value/Jost theorem; or
  2. a local edge-of-the-wedge chart theorem whose domain is explicitly local
     over a real edge `E` and whose conclusion identifies the adjacent
     branch-difference boundary value, without claiming that a point
     permutation is implemented by a Lorentz transformation on a full
     ambient tube.

  The following older theorem surface is retracted and must not be promoted to
  Lean:

  ```lean
  theorem BHW.localAdjacentOS45OppositeWedgeChart_at_jostSeed
      (hd : 2 ≤ d)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (x0 : NPointDomain d n)
      (ρ : Equiv.Perm (Fin n))
      (hx0_jost : x0 ∈ BHW.JostSet d n)
      (hx0_ET : BHW.realEmbed x0 ∈ BHW.ExtendedTube d n)
      (hx0_swapET :
        BHW.realEmbed
          (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
      (hx0_ordered :
        x0 ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
      (hx0_swap_ordered :
        (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
      ∃ (Vraw : Set (NPointDomain d n))
        (m : ℕ)
        (C : Set (Fin m → ℝ))
        (center : Fin n → Fin (d + 1) → ℂ)
        (chartCLE :
          (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin m → ℂ))
        (realChartCoord : NPointDomain d n → Fin m → ℝ)
        (E : Set (Fin m → ℝ)),
        center = BHW.realEmbed x0 ∧
        x0 ∈ Vraw ∧
        IsOpen Vraw ∧ IsConnected Vraw ∧ Vraw.Nonempty ∧
        (∀ x ∈ Vraw, x ∈ BHW.JostSet d n) ∧
        (∀ x ∈ Vraw, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
        (∀ x ∈ Vraw,
          BHW.realEmbed
            (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
        (∀ x ∈ Vraw,
          x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ) ∧
        (∀ x ∈ Vraw,
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            EuclideanOrderedPositiveTimeSector (d := d) (n := n)
              ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) ∧
        Continuous realChartCoord ∧
        IsOpen E ∧ IsConnected E ∧ E.Nonempty ∧
        IsOpen C ∧ Convex ℝ C ∧ C.Nonempty ∧
        (0 : Fin m → ℝ) ∉ C ∧
        (∀ t y, 0 < t → y ∈ C → t • y ∈ C) ∧
        (∀ x ∈ Vraw,
          chartCLE ((fun k => wickRotatePoint (x k)) - center) ∈
            SCV.TubeDomain C) ∧
        (∀ x ∈ Vraw,
          chartCLE (BHW.realEmbed x - center) =
            SCV.realEmbed (realChartCoord x)) ∧
        (∀ x ∈ Vraw, realChartCoord x ∈ E) ∧
        (∀ u ∈ SCV.TubeDomain C,
          BHW.permAct (d := d) ρ (center + chartCLE.symm u) ∈
            BHW.ForwardTube d n) ∧
        (∀ u ∈ SCV.TubeDomain C,
          BHW.permAct (d := d)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
            (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
              (center + chartCLE.symm u)) ∈
            BHW.ForwardTube d n) ∧
        (∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
          BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
            (center + chartCLE.symm u) ∈
            BHW.ExtendedTube d n) ∧
        (∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
          BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
            (center + chartCLE.symm u) ∈
            BHW.ExtendedTube d n) ∧
        (∀ y ∈ E,
          BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
            (center + chartCLE.symm (SCV.realEmbed y)) ∈
            BHW.ExtendedTube d n) ∧
        (∀ y ∈ E,
          BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
            (center + chartCLE.symm (SCV.realEmbed y)) ∈
            BHW.ExtendedTube d n) ∧
        (∀ u ∈ SCV.TubeDomain C,
          ∃ Λ : ComplexLorentzGroup d,
            BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
                (center + chartCLE.symm u) =
              BHW.complexLorentzAction Λ
                (BHW.permAct (d := d) ρ
                  (center + chartCLE.symm u))) ∧
        (∀ u ∈ SCV.TubeDomain C,
          ∃ Λ : ComplexLorentzGroup d,
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                (center + chartCLE.symm u) =
              BHW.complexLorentzAction Λ
                (BHW.permAct (d := d)
                  ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
                  (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                    (center + chartCLE.symm u))))
  ```

  The old proof transcript for
  `BHW.localAdjacentOS45OppositeWedgeChart_at_jostSeed` is retracted with the
  statement.  The only reusable piece is the ordered-Wick seed membership:
  `BHW.permAct ρ (wick x0) ∈ BHW.ForwardTube d n` and
  `BHW.permAct (τ.symm * ρ) (BHW.permAct τ (wick x0)) ∈
  BHW.ForwardTube d n`.  Those are ordinary forward-tube source-domain facts;
  they do not imply that the unpermuted or swapped branch point is an ordinary
  extended-tube point via a Lorentz transform.

  Surviving implementation pieces from this retracted theorem:

  1. First expose the permutation and ordered-Wick helpers as small public
     lemmas, because these are routine and should not be hidden inside the hard
     BHW/Jost proof.  These helper lemmas are now implemented in
     `OSReconstruction/Wightman/Reconstruction/WickRotation/OS45LocalOppositeWedge.lean`:

     ```lean
     @[simp] theorem BHW.permAct_one
         (z : Fin n → Fin (d + 1) → ℂ) :
         BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)) z = z

     theorem BHW.permAct_mul
         (π τ : Equiv.Perm (Fin n))
         (z : Fin n → Fin (d + 1) → ℂ) :
         BHW.permAct (d := d) (π * τ) z =
           BHW.permAct (d := d) τ (BHW.permAct (d := d) π z)

     theorem BHW.permAct_wickRotatePoint
         (σ : Equiv.Perm (Fin n))
         (x : NPointDomain d n) :
         BHW.permAct (d := d) σ (fun k => wickRotatePoint (x k)) =
           fun k => wickRotatePoint (x (σ k))
     ```

     Check the multiplication orientation against the actual definition of
     `BHW.permAct`; the private helper in
     `Connectedness/BHWPermutation/PermutationFlow.lean` currently proves this
     orientation by `simp [permAct, Equiv.Perm.mul_apply]`.  The public theorem
     must match that orientation exactly.

  2. Then isolate the ordered-Wick seed lemma.  This lemma is also implemented
     in `OS45LocalOppositeWedge.lean`:

     ```lean
     theorem BHW.os45_adjacent_orderedWickSeeds_mem_forwardTube
         (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
         (x : NPointDomain d n)
         (ρ : Equiv.Perm (Fin n))
         (hx_ordered :
           x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
         (hx_swap_ordered :
           (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
             EuclideanOrderedPositiveTimeSector (d := d) (n := n)
               ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
         BHW.permAct (d := d) ρ (fun k => wickRotatePoint (x k)) ∈
             BHW.ForwardTube d n ∧
         BHW.permAct (d := d)
             ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
             (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
               (fun k => wickRotatePoint (x k))) ∈
             BHW.ForwardTube d n
     ```

     The first component is
     `wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector`.  The second
     component first rewrites
     `BHW.permAct τ (wick x)` to `wick (x ∘ τ)`, then applies the same theorem
     with order label `τ.symm * ρ`.

  3. The attempted hard geometric core below has been rejected.  It is not a
     valid theorem slot, because the full-dimensional `pos_orbit_*`
     conclusions would force a nontrivial point permutation to be Lorentz on a
     generic open set.  It was briefly present in
     `OS45LocalOppositeWedge.lean` as a theorem-level WIP `sorry`, but has now
     been removed.  Keep this statement only as a negative test when designing
     the replacement:

     ```lean
     theorem BHW.localAdjacentJostOppositeCone_at_seed
         (hd : 2 ≤ d)
         (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
         (x0 : NPointDomain d n)
         (ρ : Equiv.Perm (Fin n))
         (hx0_jost : x0 ∈ BHW.JostSet d n)
         (hx0_ET : BHW.realEmbed x0 ∈ BHW.ExtendedTube d n)
         (hx0_swapET :
           BHW.realEmbed
             (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
             BHW.ExtendedTube d n)
         (hseedFT_id :
           BHW.permAct (d := d) ρ (fun k => wickRotatePoint (x0 k)) ∈
             BHW.ForwardTube d n)
         (hseedFT_swap :
           BHW.permAct (d := d)
             ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
             (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
               (fun k => wickRotatePoint (x0 k))) ∈
             BHW.ForwardTube d n) :
         ∃ (m : ℕ)
           (C : Set (Fin m → ℝ))
           (center : Fin n → Fin (d + 1) → ℂ)
           (chartCLE :
             (Fin n → Fin (d + 1) → ℂ) ≃L[ℂ] (Fin m → ℂ))
           (realChartCoord : NPointDomain d n → Fin m → ℝ)
           (E : Set (Fin m → ℝ)),
           center = BHW.realEmbed x0 ∧
           Continuous realChartCoord ∧
           IsOpen E ∧ IsConnected E ∧ E.Nonempty ∧
           IsOpen C ∧ Convex ℝ C ∧ C.Nonempty ∧
           (0 : Fin m → ℝ) ∉ C ∧
           (∀ t y, 0 < t → y ∈ C → t • y ∈ C) ∧
           chartCLE ((fun k => wickRotatePoint (x0 k)) - center) ∈
             SCV.TubeDomain C ∧
           chartCLE (BHW.realEmbed x0 - center) =
             SCV.realEmbed (realChartCoord x0) ∧
           realChartCoord x0 ∈ E ∧
           (∀ u ∈ SCV.TubeDomain C,
             BHW.permAct (d := d) ρ (center + chartCLE.symm u) ∈
               BHW.ForwardTube d n) ∧
           (∀ u ∈ SCV.TubeDomain C,
             BHW.permAct (d := d)
               ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
               (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                 (center + chartCLE.symm u)) ∈
               BHW.ForwardTube d n) ∧
           (∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
             BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
               (center + chartCLE.symm u) ∈
               BHW.ExtendedTube d n) ∧
           (∀ u ∈ SCV.TubeDomain (Neg.neg '' C),
             BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
               (center + chartCLE.symm u) ∈
               BHW.ExtendedTube d n) ∧
           (∀ y ∈ E,
             BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
               (center + chartCLE.symm (SCV.realEmbed y)) ∈
               BHW.ExtendedTube d n) ∧
           (∀ y ∈ E,
             BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
               (center + chartCLE.symm (SCV.realEmbed y)) ∈
               BHW.ExtendedTube d n) ∧
           (∀ u ∈ SCV.TubeDomain C,
             ∃ Λ : ComplexLorentzGroup d,
               BHW.permAct (d := d) (1 : Equiv.Perm (Fin n))
                   (center + chartCLE.symm u) =
                 BHW.complexLorentzAction Λ
                   (BHW.permAct (d := d) ρ
                     (center + chartCLE.symm u))) ∧
           (∀ u ∈ SCV.TubeDomain C,
             ∃ Λ : ComplexLorentzGroup d,
               BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
                   (center + chartCLE.symm u) =
                 BHW.complexLorentzAction Λ
                   (BHW.permAct (d := d)
                     ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
                     (BHW.permAct (d := d)
                       (Equiv.swap i ⟨i.val + 1, hi⟩)
                       (center + chartCLE.symm u))))
     ```

     This rejected theorem is not a mathematical BHW/Jost core.  It returns no
     `Vraw`, but more importantly its full-dimensional orbit conclusions are
     false for generic configurations.  Do not reintroduce this statement as a
     placeholder, structure field, theorem-level `sorry`, or axiom.  The
     temporary production `sorry` was removed from
     `OS45LocalOppositeWedge.lean`, and the direct-sorry census was restored.

  4. The real-ball shrink is a separate topology theorem over the chart core:

     Its production conclusion is:

     ```lean
     ∃ Vraw : Set (NPointDomain d n),
       x0 ∈ Vraw ∧
       IsOpen Vraw ∧ IsConnected Vraw ∧ Vraw.Nonempty ∧
       (∀ x ∈ Vraw, x ∈ BHW.JostSet d n) ∧
       (∀ x ∈ Vraw, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
       (∀ x ∈ Vraw,
         BHW.realEmbed
           (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           BHW.ExtendedTube d n) ∧
       (∀ x ∈ Vraw,
         x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ) ∧
       (∀ x ∈ Vraw,
         (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
           EuclideanOrderedPositiveTimeSector (d := d) (n := n)
             ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) ∧
       (∀ x ∈ Vraw,
         chartCLE ((fun k => wickRotatePoint (x k)) - center) ∈
           SCV.TubeDomain C) ∧
       (∀ x ∈ Vraw,
         chartCLE (BHW.realEmbed x - center) =
           SCV.realEmbed (realChartCoord x)) ∧
       (∀ x ∈ Vraw, realChartCoord x ∈ E)
     ```

     The proof is `exists_connected_open_ball_subset` applied to the open
     intersection of the field preimages.  This step is Lean-topological, not a
     new BHW theorem.

  5. The composition into
     `BHW.localAdjacentOS45OppositeWedgeChart_at_jostSeed` is also retracted,
     because its hard core is false as stated.  The correct response is not to
     add a conditional wrapper around the same orbit fields.  The replacement
     must either invoke a genuine BHW/PET branch theorem or use a local EOW
     branch-difference chart whose hypotheses and conclusions stay local over
     the real edge.

  The older pure-geometry theorem below is likewise retracted.  It is useful
  only as a record of what not to ask from BHW/Jost geometry:

  ```lean
  theorem os45_adjacent_localBHWJostOrbitChart_at_seed
      (hd : 2 ≤ d)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (x0 : NPointDomain d n)
      (ρ : Equiv.Perm (Fin n))
      (hx0_jost : x0 ∈ BHW.JostSet d n)
      (hx0_ET : BHW.realEmbed x0 ∈ BHW.ExtendedTube d n)
      (hx0_swapET :
        BHW.realEmbed
          (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n)
      (hx0_ordered :
        x0 ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
      (hx0_swap_ordered :
        (fun k => x0 (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          EuclideanOrderedPositiveTimeSector (d := d) (n := n)
            ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
      ∃ V₀ : Set (NPointDomain d n),
        x0 ∈ V₀ ∧
        Nonempty
          (OS45AdjacentSingleEOWGeometry (d := d) n i hi V₀ ρ)
  ```

  This theorem is pure BHW/SCV geometry.  It should live with the BHW/Jost
  local geometry support, not in the OS analytic files.  Its proof transcript
  should be:

  The replacement transcript must start from the same safe ordered-Wick seed
  lemma, but after that it must **not** ask for
  `BHW.localAdjacentOS45OppositeWedgeChart_at_jostSeed`, `pos_orbit_id`, or
  `pos_orbit_swap`.  The missing proof-doc item is now the exact OS §4.5
  branch-difference theorem:

  1. use E3 to get adjacent Euclidean branch equality on the Wick edge;
  2. use the OS §4.5 ACR(1) continuation and the external BHW/Jost theorem to
     identify the common analytic branch on the relevant PET/Jost boundary;
  3. recover equality of the real-Jost adjacent branch difference by boundary
     values;
  4. only then package the compact-test edge witness.

  If a local chart formulation is still preferred, its domain must be a local
  wedge over a real edge `E`, not the full ambient `SCV.TubeDomain C`, and its
  conclusion must be equality of branch-difference boundary values, not
  existence of Lorentz transformations implementing point permutations.

  The preliminary concrete geometry theorem is:

  ```lean
  theorem choose_os45_singleEOWChart_preedge_for_adjacent_swap
      (hd : 2 ≤ d)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
      ∃ (V₀ : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n)),
        Nonempty
          (OS45AdjacentSingleEOWGeometry (d := d) n i hi V₀ ρ)
  ```

  Proof transcript:

  1. start from `adjacent_overlap_real_jost_witness_exists` and perturb it by
     `exists_ordered_small_time_perturb_in_adjacent_overlap`;
  2. apply
     `os45_adjacent_localBHWJostOrbitChart_at_seed` at the resulting real Jost
     point and order label.  This theorem already performs the preliminary
     ball shrink and exports `center`, `chartCLE`, `C`, `E`, the real
     coordinate map, the positive/negative/edge domain inclusions, and the
     two `pos_orbit_*` witnesses;
  3. return the `V₀`, `ρ`, and `Nonempty
     (OS45AdjacentSingleEOWGeometry ...)` from that theorem.  The selector
     should not re-prove or weaken any of the local BHW/Jost orbit fields.

  Important correction: this pure geometry selector is not, by itself, the
  final production selector.  Its `V₀` is only a preliminary small real edge on
  which the chart and all raw Jost/ET/order fields are valid.  The EOW theorem
  returns an open chart-domain
  `Uc`, and the proof must know that the Wick section
  `x ↦ chartCLE (wick(x) - center)` lands in `Uc`.  That membership generally
  cannot be fixed before the EOW theorem is applied, because `Uc` is produced by
  the analytic construction.  The final real ball `V` should therefore be
  chosen as a subset of `V₀` **after** applying EOW, by shrinking around the
  seed inside the open preimages of:

  - the Jost/ET/swap-ET/order conditions;
  - the real-edge chart set `E`;
  - the pulled-back EOW domain `Uc`;
  - the positive-tube chart condition for the Wick section.

  Thus the preferred production theorem is the combined selector-and-envelope
  statement:

  ```lean
  theorem os45_adjacent_branchDifferenceEnvelope_and_edge_exists_singleChart
      (hd : 2 ≤ d)
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
      ∃ (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n))
        (U : Set (Fin n → Fin (d + 1) → ℂ))
        (H : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
        (∀ x ∈ V, x ∈ BHW.JostSet d n) ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
        (∀ x ∈ V,
          BHW.realEmbed
            (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
        (∀ x ∈ V,
          x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ) ∧
        (∀ x ∈ V,
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            EuclideanOrderedPositiveTimeSector (d := d) (n := n)
              ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) ∧
        IsOpen U ∧ IsConnected U ∧
        DifferentiableOn ℂ H U ∧
        (∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U) ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
        (∀ x ∈ V,
          H (fun k => wickRotatePoint (x k)) =
            OS45AdjacentWickDifference (d := d) OS lgc n i hi ρ
              (fun k => wickRotatePoint (x k))) ∧
        (∀ x ∈ V,
          H (BHW.realEmbed x) =
            OS45AdjacentRealDifference (d := d) OS lgc n i hi
              (BHW.realEmbed x))
  ```

  Proof transcript for the combined theorem:

  1. construct the seed, order label, affine chart, cone, and edge set by the
     pure local BHW/Jost geometry theorem, obtaining a preliminary edge
     `V₀`, a label `ρ`, and
     `G : OS45AdjacentSingleEOWGeometry d n i hi V₀ ρ`;
  2. prove the branch-difference common boundary value in that chart;
  3. apply `SCV.edge_of_the_wedge_theorem_connected_of_connected_edge`, getting
     `Uc` and `Hc`;
  4. define the pulled-back complex domain
     `U := {z | chartCLE (z - center) ∈ Uc}` and
     `H z := Hc (chartCLE (z - center))`;
  5. choose the final edge `V := Metric.ball xseed r` by the post-EOW shrink
     lemma below, with `V ⊆ V₀` and all chart-domain memberships;
  6. export the Jost/ET/order fields by `V ⊆ V₀` and the fields of `G`.  Export
     the Wick trace from the positive-tube agreement clause, and export the real
     trace by rewriting
     `chartCLE (realEmbed x - center) = SCV.realEmbed (realChartCoord x)` and
     using the EOW real-edge value at `realChartCoord x`.

  The post-EOW shrink should be isolated as a routine topology lemma, because
  it is exactly where several open conditions are synchronized:

  ```lean
  theorem os45_singleChart_postEOW_shrink
      (V₀ : Set (NPointDomain d n))
      (ρ : Equiv.Perm (Fin n))
      (G : OS45AdjacentSingleEOWGeometry (d := d) n i hi V₀ ρ)
      (xseed : NPointDomain d n)
      (hxseed : xseed ∈ V₀)
      (Uc : Set (Fin G.m → ℂ))
      (hUc_open : IsOpen Uc)
      (hUc_edge : ∀ y ∈ G.E, SCV.realEmbed y ∈ Uc) :
      ∃ V : Set (NPointDomain d n),
        IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
        xseed ∈ V ∧
        V ⊆ V₀ ∧
        (∀ x ∈ V, G.realChartCoord x ∈ G.E) ∧
        (∀ x ∈ V,
          G.chartCLE ((fun k => wickRotatePoint (x k)) - G.center) ∈
            Uc ∩ SCV.TubeDomain G.C) ∧
        (∀ x ∈ V,
          G.chartCLE (BHW.realEmbed x - G.center) ∈ Uc)
  ```

  Proof transcript for `os45_singleChart_postEOW_shrink`:

  1. define the final admissible set

     ```lean
     Sfinal :=
       V₀ ∩
       {x | G.realChartCoord x ∈ G.E} ∩
       {x | G.chartCLE ((fun k => wickRotatePoint (x k)) - G.center) ∈
         Uc ∩ SCV.TubeDomain G.C} ∩
       {x | G.chartCLE (BHW.realEmbed x - G.center) ∈ Uc}
     ```

  2. prove `IsOpen Sfinal`.  Use `G.V_open`, `G.E_open`,
     `SCV.tubeDomain_isOpen G.C_open`, `hUc_open`, continuity of
     `G.realChartCoord`, continuity of `continuous_wickRotateRealConfig`,
     continuity of `BHW.realEmbed`, and continuity of the affine maps
     `z ↦ z - G.center` and `G.chartCLE`;
  3. prove `xseed ∈ Sfinal`.  The first three components come from
     `hxseed`, `G.real_coord_mem xseed hxseed`, and `G.wick_coord xseed hxseed`.
     For the real `Uc` component, rewrite by
     `G.real_coord_eq xseed hxseed` and use
     `hUc_edge (G.realChartCoord xseed) (G.real_coord_mem xseed hxseed)`;
  4. apply `exists_connected_open_ball_subset hSfinal_open hxseedSfinal` to get
     `V := Metric.ball xseed r` with `V ⊆ Sfinal`;
  5. all exported fields are projections of `V ⊆ Sfinal`.

  The pullback from chart coordinates to absolute coordinates should also be
  factored explicitly.  Define the affine chart homeomorphism associated to
  `G`:

  ```lean
  noncomputable def OS45AdjacentSingleEOWGeometry.affineChartHomeomorph
      (G : OS45AdjacentSingleEOWGeometry (d := d) n i hi V₀ ρ) :
      (Fin n → Fin (d + 1) → ℂ) ≃ₜ (Fin G.m → ℂ) where
    toFun z := G.chartCLE (z - G.center)
    invFun u := G.center + G.chartCLE.symm u
    left_inv := by
      intro z
      -- `G.center + G.chartCLE.symm (G.chartCLE (z - G.center)) = z`
      simp
    right_inv := by
      intro u
      -- `G.chartCLE (G.center + G.chartCLE.symm u - G.center) = u`
      simp
    continuous_toFun := by
      -- continuity of subtraction by a constant and of `G.chartCLE`
      continuity
    continuous_invFun := by
      -- continuity of addition of a constant and of `G.chartCLE.symm`
      continuity
  ```

  With this helper, the coordinate EOW output pulls back mechanically:

  ```lean
  theorem os45_singleChart_pullback_EOW_output
      (G : OS45AdjacentSingleEOWGeometry (d := d) n i hi V₀ ρ)
      (V : Set (NPointDomain d n))
      (Uc : Set (Fin G.m → ℂ))
      (Hc : (Fin G.m → ℂ) → ℂ)
      (hUc_open : IsOpen Uc)
      (hUc_connected : IsConnected Uc)
      (hHc_holo : DifferentiableOn ℂ Hc Uc)
      (hHc_pos :
        ∀ u ∈ Uc ∩ SCV.TubeDomain G.C,
          Hc u =
            OS45AdjacentWickDifference (d := d) OS lgc n i hi ρ
              (G.center + G.chartCLE.symm u))
      (hHc_edge :
        ∀ y ∈ G.E, Hc (SCV.realEmbed y) =
          OS45AdjacentRealDifference (d := d) OS lgc n i hi
            (G.center + G.chartCLE.symm (SCV.realEmbed y))) :
      ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
        (H : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        U = (G.affineChartHomeomorph ⁻¹' Uc) ∧
        H = (fun z => Hc (G.chartCLE (z - G.center))) ∧
        IsOpen U ∧ IsConnected U ∧ DifferentiableOn ℂ H U ∧
        (∀ x ∈ V,
          G.chartCLE ((fun k => wickRotatePoint (x k)) - G.center) ∈
            Uc ∩ SCV.TubeDomain G.C →
          H (fun k => wickRotatePoint (x k)) =
            OS45AdjacentWickDifference (d := d) OS lgc n i hi ρ
              (fun k => wickRotatePoint (x k))) ∧
        (∀ x ∈ V,
          G.realChartCoord x ∈ G.E →
          G.chartCLE (BHW.realEmbed x - G.center) =
            SCV.realEmbed (G.realChartCoord x) →
          H (BHW.realEmbed x) =
            OS45AdjacentRealDifference (d := d) OS lgc n i hi
              (BHW.realEmbed x))
  ```

  Proof transcript for `os45_singleChart_pullback_EOW_output`:

  1. set `A := G.affineChartHomeomorph`,
     `U := A ⁻¹' Uc`, and `H z := Hc (A z)`;
  2. `IsOpen U` is `hUc_open.preimage A.continuous`;
  3. `IsConnected U` follows from `hUc_connected` transported by the
     homeomorphism `A.symm`/`A`; equivalently rewrite `U = A.symm '' Uc` and
     use continuity of `A.symm`;
  4. `DifferentiableOn ℂ H U` is `hHc_holo` composed with the continuous-linear
     part of the affine chart.  In Lean, prove a small local lemma that
     `fun z => G.chartCLE (z - G.center)` is differentiable everywhere, then
     apply `DifferentiableOn.comp`;
  5. for the Wick trace, the post-EOW shrink gives
     `A (wick x) ∈ Uc ∩ TubeDomain G.C`; use `hHc_pos` and the inverse identity
     `G.center + G.chartCLE.symm (A (wick x)) = wick x`;
  6. for the real trace, use
     `G.real_coord_eq x hx` to rewrite `A (realEmbed x)` as
     `SCV.realEmbed (G.realChartCoord x)`, then use `hHc_edge` and the inverse
     identity.  This avoids any one-branch Wick-to-real comparison.

  The OS-dependent boundary-value part is then a theorem over this geometry:

  ```lean
  theorem os45_adjacent_singleChart_commonBoundaryValue
      (OS : OsterwalderSchraderAxioms d)
      (lgc : OSLinearGrowthCondition d OS)
      (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (V : Set (NPointDomain d n)) (ρ : Equiv.Perm (Fin n))
      (G : OS45AdjacentSingleEOWGeometry (d := d) n i hi V ρ) :
      ∃ bv : (Fin G.m → ℝ) → ℂ,
        ContinuousOn bv G.E ∧
        (∀ y ∈ G.E,
          bv y =
            OS45AdjacentRealDifference (d := d) OS lgc n i hi
              (G.center + G.chartCLE.symm (SCV.realEmbed y))) ∧
        (∀ y ∈ G.E,
          Filter.Tendsto
            (fun u =>
              OS45AdjacentWickDifference (d := d) OS lgc n i hi ρ
                (G.center + G.chartCLE.symm u))
            (nhdsWithin (SCV.realEmbed y) (SCV.TubeDomain G.C))
            (nhds (bv y))) ∧
        (∀ y ∈ G.E,
          Filter.Tendsto
            (fun u =>
              OS45AdjacentRealDifference (d := d) OS lgc n i hi
                (G.center + G.chartCLE.symm u))
            (nhdsWithin (SCV.realEmbed y)
              (SCV.TubeDomain (Neg.neg '' G.C)))
            (nhds (bv y)))
  ```

  Proof transcript for `os45_adjacent_singleChart_commonBoundaryValue`:

  1. Set

     ```lean
     f_plus u :=
       OS45AdjacentWickDifference (d := d) OS lgc n i hi ρ
         (G.center + G.chartCLE.symm u)

     f_minus u :=
       OS45AdjacentRealDifference (d := d) OS lgc n i hi
         (G.center + G.chartCLE.symm u)
     ```

  2. This old branchwise step is also retracted in its `G.pos_orbit_*` form.
     A corrected theorem may still apply a branch-difference OS §4.5/BHW-Jost
     boundary theorem, but it must obtain the positive-side identification from
     the common analytic continuation / PET branch theorem, not from local
     Lorentz orbit witnesses for point permutations.
  3. Let `bv_id` and `bv_τ` be the branchwise boundary values and set
     `bv y := bv_τ y - bv_id y`.
  4. Continuity of `bv` follows by subtraction.
  5. The real-edge formula unfolds to `f_minus (SCV.realEmbed y)` by the
     definitions of `OS45AdjacentRealDifference`, `OS45RealChart`, and the two
     branchwise real-edge formulas.
  6. The positive-wedge and negative-wedge Tendsto fields are obtained by
     subtracting the two branchwise Tendsto statements.  This is only a common
     boundary-value statement for the adjacent branch **difference**; it does
     not assert any one-branch Wick-to-real equality.

  The EOW call inside the combined theorem should then use the exact coordinate
  functions above:

  ```lean
  have hf_plus :
      DifferentiableOn ℂ f_plus (SCV.TubeDomain G.C)

  have hf_minus :
      DifferentiableOn ℂ f_minus (SCV.TubeDomain (Neg.neg '' G.C))

  obtain ⟨Uc, Hc, hUc_open, hUc_connected, hUc_edge_mem, hHc_holo,
      hHc_edge_value, hHc_pos, hHc_neg, hHc_unique⟩ :=
    SCV.edge_of_the_wedge_theorem_connected_of_connected_edge
      G.C G.C_open G.C_convex G.C_not_zero G.C_cone G.C_nonempty
      f_plus f_minus hf_plus hf_minus
      G.E G.E_open G.E_connected bv hbv_cont
      hf_plus_bv hf_minus_bv
  ```

  The proof of `hf_plus` is: `G.pos_domain` maps the positive tube into
  `OS45AdjacentWickDifferenceDomain`; compose holomorphy of
  `OS45AdjacentWickDifference` on that domain with the affine map
  `u ↦ G.center + G.chartCLE.symm u`.  The proof of `hf_minus` is identical
  with `G.neg_domain` and `OS45AdjacentRealDifferenceDomain`.

  Here `hHc_pos` is the agreement clause later used for the Wick trace, while
  `hUc_edge_mem` and `hHc_edge_value` are used for the real trace and for the
  post-EOW shrink.  The negative-tube agreement is retained for uniqueness but
  is not needed by the final compact-test consumer.

  Do not implement a separate fixed-`V`
  `os45_adjacent_branchDifferenceEnvelope_exists_singleChart` theorem unless
  its hypotheses explicitly include the post-EOW membership
  `∀ x ∈ V, chartCLE (wick(x) - center) ∈ Uc`.  Without that field, the proof
  cannot show the Wick section lies in the pulled-back EOW domain.  The
  production-safe surface is the combined selector-and-envelope theorem above,
  where `V` is shrunk after `Uc` is known.

  If the combined single-chart theorem is implemented, the broader
  `SCV.differenceEnvelope_of_localBoundaryCharts` can be deferred.  If the
  single-chart shrink fails, then the fallback is the generic local chart
  gluing theorem above; do not add another wrapper around the same seam.
6. Fill either the existing `AdjacentOSEOWEnvelope` record from genuine
   one-branch continuations, or replace the downstream consumer by the sharper
   difference-envelope theorem above.  In either case, no field may be supplied
   by a dummy total function or by a non-mathematical choice.

For Lean implementation the sharper packet should be:

```lean
structure AdjacentOSEOWDifferenceEnvelope
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (τ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n)) where
  U : Set (Fin n → Fin (d + 1) → ℂ)
  U_open : IsOpen U
  U_connected : IsConnected U
  H : (Fin n → Fin (d + 1) → ℂ) → ℂ
  H_holo : DifferentiableOn ℂ H U
  wick_mem :
    ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U
  real_mem :
    ∀ x ∈ V, BHW.realEmbed x ∈ U
  wick_diff :
    ∀ x ∈ V,
      H (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (τ k))) -
        bvt_F OS lgc n (fun k => wickRotatePoint (x k))
  real_diff :
    ∀ x ∈ V,
      H (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (τ k))) -
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
```

Given this envelope, the compact-test edge theorem is mechanical and should be
proved separately:

```lean
theorem bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (E : AdjacentOSEOWDifferenceEnvelope (d := d) OS lgc n
      (Equiv.swap i ⟨i.val + 1, hi⟩) V) :
    ∀ φ : SchwartzNPoint d n,
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  intro φ hφ_compact hφ_tsupport
  have hEqOn :
      Set.EqOn E.H (fun _ => 0) E.U := by
    refine
      eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
        (d := d) (n := n)
        E.U V E.U_open E.U_connected hV_open hV_nonempty
        E.wick_mem E.H (fun _ => 0) E.H_holo
        (by intro z hz; exact differentiableWithinAt_const _ _) ?_
    intro ψ hψ_compact hψ_tsupport
    -- Rewrite by `E.wick_diff`, then use the E3 compact equality from part B.
    simpa [E.wick_diff] using
      bvt_F_euclidean_adjacent_branch_pairing_eq_from_E3
        (d := d) OS lgc n i hi V hV_jost ψ hψ_tsupport
  -- Specialize at the real edge and rewrite by `E.real_diff`.
  have hpoint :
      ∀ x ∈ V,
        BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
    intro x hx
    have h := hEqOn (BHW.realEmbed x) (E.real_mem x hx)
    have hsub :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed
              (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) -
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) = 0 := by
      simpa [E.real_diff x hx] using h
    exact sub_eq_zero.mp hsub
  -- Integrands agree on `V`; outside `tsupport φ`, `φ = 0`.
  exact integral_eq_of_tsupport_subset_of_pointwise_on
    (d := d) (n := n) V
    (fun x =>
      BHW.extendF (bvt_F OS lgc n)
        (BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))))
    (fun x =>
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x))
    φ hφ_tsupport hpoint
```

The helper `integral_eq_of_tsupport_subset_of_pointwise_on` is the standard
support-zero bookkeeping lemma, but it should still be a named Lean lemma, not
an inline proof repeated at the edge frontier:

```lean
theorem integral_eq_of_tsupport_subset_of_pointwise_on
    (V : Set (NPointDomain d n))
    (A B : NPointDomain d n → ℂ)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport :
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V)
    (hAB : ∀ x ∈ V, A x = B x) :
    ∫ x : NPointDomain d n, A x * φ x =
      ∫ x : NPointDomain d n, B x * φ x := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxV : x ∈ V
  · simp [hAB x hxV]
  · have hx_not_tsupport :
        x ∉ tsupport (φ : NPointDomain d n → ℂ) := by
      intro hx
      exact hxV (hφ_tsupport hx)
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_tsupport
    simp [hφx]
```

This lemma uses no integrability assumptions because the Bochner integral is
congruent under a.e. equality.  The only support fact needed is
`image_eq_zero_of_notMem_tsupport`, already used elsewhere in the repo.

The theorem consumed by `SelectedAdjacentPermutationEdgeData` should now return
the edge witness, because the final `V` is chosen after the single-chart EOW
domain is known:

```lean
theorem bvt_F_adjacent_edgeWitness_from_OS_ACR_of_two_le
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧ IsConnected V ∧ V.Nonempty ∧
      (∀ x ∈ V, x ∈ BHW.JostSet d n) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHW.ExtendedTube d n) ∧
      (∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.realEmbed
                (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
          =
        ∫ x : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)
```

with proof:

1. obtain `V`, `ρ`, `U`, `H`, and all edge/envelope fields from
   `os45_adjacent_branchDifferenceEnvelope_and_edge_exists_singleChart`;
2. build an `AdjacentOSEOWDifferenceEnvelope` from these fields;
3. fill `AdjacentOSEOWDifferenceEnvelope.wick_diff` by simplifying the two
   Wick chart fields with `bvt_F_perm` and
   `τ ((τ.symm * ρ) k) = ρ k`;
4. fill `AdjacentOSEOWDifferenceEnvelope.real_diff` directly from the real-edge
   field of the combined single-chart theorem;
5. apply
   `bvt_F_adjacent_extendF_edgeDistribution_eq_of_osEOWDifferenceEnvelope`.
6. return `V` with `hV_open`, `hV_connected`, `hV_nonempty`, `hV_jost`,
   `hV_ET`, `hV_swapET`, and the compact-test equality.

The exact combined single-chart selector/envelope theorem is now the main
proof-doc gap in this OS-internal packet.  It must mention ACR/EOW geometry,
post-EOW shrinking of `V`, and local adjacent branch identification, not PET
global monodromy and not one-branch Wick-to-real equality.  Once that theorem is
proved, the compact-test theorem above is ready for Lean implementation modulo
routine support-zero and `simp` orientation details.

**D. Package `SelectedAdjacentPermutationEdgeData`.**

Once A-C are proved, the final constructor is routine:

```lean
theorem bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SelectedAdjacentPermutationEdgeData OS lgc n := by
  refine ⟨?overlap_connected, ?edge_witness⟩
  · intro i hi
    simpa [BHW.adjSwapExtendedOverlapSet, BHW.permAct] using
      BHW.isConnected_adjSwapExtendedOverlap (d := d) n i hi
  · intro i hi
    obtain ⟨V, hV_open, hV_connected, hV_ne, hV_jost, hV_ET, hV_swapET,
      hEdgeEq⟩ :=
      bvt_F_adjacent_edgeWitness_from_OS_ACR_of_two_le
        (d := d) hd OS lgc n i hi
    refine ⟨V, hV_open, hV_ne, hV_ET, hV_swapET, ?_⟩
    exact hEdgeEq
```

Readiness status after the #1104 orbit-invariant audit: A and the final
packaging are close to implementation; B is Lean-routine but must be checked
for inverse-permutation orientation.  C is **not** implementation-ready.  The
previous preferred single-chart theorem surface
`BHW.localAdjacentOS45OppositeWedgeChart_at_jostSeed` has been rejected because
its positive orbit witnesses would make a point permutation into a Lorentz
transformation on a full-dimensional tube.  The hard ingredient to document
next is instead a corrected OS §4.5 branch-difference supplier:
either a generic BHW/PET branch theorem plus Jost boundary-value transfer, or a
local edge-wedge chart theorem with genuinely local domain over `E` and no
full-tube `pos_orbit_*` fields.  The broader
`SCV.differenceEnvelope_of_localBoundaryCharts` remains a possible SCV
implementation tool only after that corrected local theorem shape is written
down.  None of these may be replaced by a hidden envelope field, a wrapper
theorem, a one-branch Wick-to-real comparison, or a point-permutation
Lorentz-orbit witness on a generic open set.
This packaging theorem is now explicitly the `2 ≤ d` real-edge supplier.  The
all-`[NeZero d]` theorem-2 supplier is not implementation-ready until the
`d = 1` complex-edge replacement is specified.

### 0.1. Checked production inventory and current trap

Theorem-2 work spans several support layers, so this blueprint now fixes the
checked file inventory before any Lean implementation resumes:

- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OS45LocalOppositeWedge.lean`
- `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
- `OSReconstruction/ComplexLieGroups/JostPoints.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`

Planned small support file for the next implementation batch:

- `OSReconstruction/Wightman/Reconstruction/WickRotation/OS45LocalOppositeWedge.lean`

This file currently contains only the public `BHW.permAct_*` helpers and the
ordered-Wick seed lemma.  It must not contain the retracted
`BHW.localAdjacentJostOppositeCone_at_seed` theorem surface.  Any replacement
for the local OS45/BHW geometry must first be rewritten here in the blueprint
at implementation level and checked against the Lorentz-invariant obstruction.
Keeping this support separate prevents the theorem-2 frontier from reopening
large stable support files unless the exact import graph forces that move.  The
location is intentional:
`wickRotatePoint` and `EuclideanOrderedPositiveTimeSector` already live in the
WickRotation layer, so placing the OS45 chart supplier under `ComplexLieGroups`
would create the wrong dependency direction.

Checked-present theorem surfaces that are useful but must be used with their
actual hypotheses:

- `BHWExtension.lean :: W_analytic_swap_boundary_pairing_eq`
- `BHWExtension.lean :: analytic_extended_local_commutativity`
- `BHWExtension.lean :: analytic_boundary_local_commutativity_of_boundary_continuous`
- `AdjacencyDistributional.lean :: extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
- `Adjacency.lean :: exists_real_open_nhds_adjSwap`
- `ForwardTubeDistributions.lean :: boundary_function_continuous_forwardTube_of_flatRegular`
- `OSToWightmanBoundaryValuesComparison.lean :: bv_local_commutativity_transfer_of_swap_pairing`
- `OSToWightmanTubeIdentity.lean :: eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen`
- `OSToWightmanTubeIdentity.lean :: EuclideanOrderedPositiveTimeSector`
- `OSToWightmanTubeIdentity.lean :: positiveTimeTranslate`
- `OSToWightmanTubeIdentity.lean :: exists_uniform_positiveTimeShift_of_compact_tsupport`
- `OSToWightmanTubeIdentity.lean :: isOpen_positiveTimeTranslate_image`
- `OSToWightmanTubeIdentity.lean :: wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector`
- `OSToWightmanTubeIdentity.lean :: positiveTimeTranslate_mem_orderedPositiveTimeSector_of_pairwise_distinct`
- `OSToWightmanTubeIdentity.lean :: timeShiftSchwartzNPoint_apply_positiveTimeTranslate`
- `OSToWightmanTubeIdentity.lean :: hasCompactSupport_timeShiftSchwartzNPoint`
- `OSToWightmanTubeIdentity.lean :: tsupport_timeShiftSchwartzNPoint_subset_positiveTimeTranslate_image`
- `OSToWightmanTubeIdentity.lean :: measure_timeCoord_eq_zero`
- `OSToWightmanTubeIdentity.lean :: ae_pairwise_distinct_timeCoords`
- `Connectedness/PermutedTube.lean :: mem_permutedExtendedTube_iff_exists_perm_mem_extendedTube`
- `Connectedness/PermutedTube.lean :: permutedExtendedTubeBranch`
- `Connectedness/PermutedTube.lean :: permutedExtendedTubeBranch_mem_extendedTube`
- `ForwardTubeLorentz.lean :: isOpen_translatedPET`
- `ForwardTubeLorentz.lean :: translatedPET_perm`
- `ForwardTubeLorentz.lean :: translatedPET_perm_iff`
- `ForwardTubeLorentz.lean :: translatedPET_value_eq_of_translation_invariant`
- `ForwardTubeLorentz.lean :: translatedPETValue`
- `ForwardTubeLorentz.lean :: translatedPETValue_eq_on_PET`
- `ForwardTubeLorentz.lean :: translatedPETValue_translation_invariant`
- `ForwardTubeLorentz.lean :: translatedPETValueTotal`
- `ForwardTubeLorentz.lean :: translatedPETValueTotal_eq_on_PET`
- `ForwardTubeLorentz.lean :: translatedPETValueTotal_translation_invariant`
- `ForwardTubeLorentz.lean :: translatedPETValue_perm_invariant`
- `ForwardTubeLorentz.lean :: translatedPETValueTotal_perm_invariant`
- `OSToWightmanBoundaryValuesBase.lean :: bvt_F_acrOne_package`
- `Connectedness/PermutedTube.lean :: permutedExtendedTubeSector`
- `Connectedness/PermutedTube.lean :: isOpen_permutedExtendedTubeSector`
- `Connectedness/PermutedTube.lean :: permutedExtendedTube_eq_iUnion_sectors`
- `Connectedness/PermutedTube.lean :: permutedExtendedTubeSector_subset_permutedExtendedTube`
- `Connectedness/PermutedTubeConnected.lean :: permutedExtendedTubeSector_isPreconnected`
- `Connectedness/PermutedTubeConnected.lean :: permutedExtendedTubeSector_adjacent_overlap_nonempty`
- `Connectedness/PermutedTubeGluing.lean :: gluedPETValue`
- `Connectedness/PermutedTubeGluing.lean :: gluedPETValue_eq_of_mem_sector`
- `Connectedness/PermutedTubeGluing.lean :: gluedPETValue_holomorphicOn`
- `Connectedness/PermutedTubeMonodromy.lean :: permutedForwardTube_sector_eq_of_mem`
- `Connectedness/PermutedTubeMonodromy.lean :: mem_extendedTube_iff_exists_lorentz_mem_forwardTube`
- `Connectedness/PermutedTubeMonodromy.lean :: petSectorAdjStep`
- `Connectedness/PermutedTubeMonodromy.lean :: petReachableLabelSet`
- `Connectedness/PermutedTubeMonodromy.lean :: petReachableLabelAdjStep`
- `Connectedness/PermutedTubeMonodromy.lean :: one_mem_petReachableLabelSet_of_forwardTube`
- `Connectedness/PermutedTubeMonodromy.lean :: mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube`
- `Connectedness/PermutedTubeMonodromy.lean :: petReachableLabelSet_adjacent_connected_of_orbitChamberConnected`
- `Connectedness/PermutedTubeMonodromy.lean :: petSectorFiber_forwardTube_chain_of_reachableLabelConnected`
- `Connectedness/PermutedTubeMonodromy.lean :: petSectorFiber_adjacent_connected_of_reachableLabelConnected`
- `Connectedness/PermutedTubeMonodromy.lean :: petSectorFiber_adjacent_connected_of_identity_chain`
- `Connectedness/PermutedTubeMonodromy.lean :: permutedExtendedTubeSector_complexLorentzAction_iff`
- `Connectedness/PermutedTubeMonodromy.lean :: petSectorFiber_identity_chain_of_forwardTube_chain`
- `Connectedness/PermutedTubeMonodromy.lean :: petSectorFiber_forwardTube_chain_of_suffixRemoval`
- `Connectedness/PermutedTubeMonodromy.lean :: extendF_pet_branch_independence_of_adjacent_of_sectorFiberConnected`
- `Connectedness/PermutedTubeMonodromy.lean :: extendF_pet_branch_independence_of_adjacent_of_reachableLabelConnected`
- `Connectedness/PermutedTubeMonodromy.lean :: extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected`
- `Connectedness/PermutedTubeMonodromy.lean :: extendF_perm_eq_on_extendedTube_of_petBranchIndependence`
- `Connectedness/PermutedTubeMonodromy.lean :: F_permutation_invariance_of_petBranchIndependence`
- `Connectedness/PermutedTubeMonodromy.lean :: fullExtendF_well_defined_of_petBranchIndependence`
- `OSToWightmanSelectedWitness.lean :: SelectedAdjacentPermutationEdgeData`
- `OSToWightmanSelectedWitness.lean :: SelectedAllPermutationEdgeData` (overstrong conditional helper only)
- `OSToWightmanSelectedWitness.lean :: bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETBranch`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETBranch_holomorphicOn_sector`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`
- `OSToWightmanSelectedWitness.lean :: bvt_F_extendF_perm_overlap_of_selectedEdgeData`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_eq_extendF_perm`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_eq_bvt_F_on_forwardTube`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_holomorphicOn_PET`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_lorentzInvariant`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedAbsolutePETGluedValue_permInvariant`
- `OSToWightmanSelectedWitness.lean :: bvt_route1AbsolutePrePullback`
- `OSToWightmanSelectedWitness.lean :: bvt_route1AbsolutePrePullback_translate`
- `OSToWightmanSelectedWitness.lean :: bvt_route1AbsolutePrePullback_eq_bvt_F_on_forwardTube`
- `OSToWightmanSelectedWitness.lean :: bvt_reducedWightmanFamily`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedReducedPreInput_factorization_absoluteApproach`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedReducedBoundaryIntegral_eq_absoluteBoundaryIntegral`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedReducedBoundaryValues`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedReducedForwardTubeInput`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData_translate`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData_translate_on_PET`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData_holomorphicOn_PET`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData_permInvariant`
- `OSToWightmanSelectedWitness.lean :: bvt_selectedPETExtensionOfReducedData_eq_bvt_F_on_forwardTube`

Important correction: the first four BHW/adjacency locality surfaces above
currently take an input of the form
`IsLocallyCommutativeWeak d W`.  When `W := bvt_W OS lgc`, that is exactly the
public theorem-2 locality conclusion being proved downstream.  Therefore none
of these theorem surfaces may be instantiated directly with
`bvt_locally_commutative` or with any equivalent global locality hypothesis for
`bvt_W OS lgc` in the theorem-2 proof.  Doing so would be circular even if the
Lean term typechecks.

The missing theorem-2 work is consequently sharper than older drafts suggested.
The primary OS-I-faithful route needs a non-circular BHW/PET permutation-edge
supplier for `extendF`, plus the geometry and transfer adapters that feed it.
The older adjacent-swap finite-shell package remains a fallback only if we
retain the current overstrong canonical-shell consumer.

### 0.2. Route-contract ledger for the missing theorem-2 package

The following names are planned theorem-package names fixed by this blueprint.
They are not assumed to exist in the current tree until implemented.

Important correction: the primary route must not prove locality by asserting
global continuity of the raw real trace
`x ↦ bvt_F OS lgc n (BHW.realEmbed x)`.  Wightman boundary values are
distributional in general.  Any `HasFourierLaplaceReprRegular` or
`boundary_continuous` package below is fallback/support context, not the primary
theorem-2 bridge.

| Slot | Home | Must consume | Must export |
| --- | --- | --- | --- |
| `choose_os45_real_open_edge_for_adjacent_swap` | `BHWPermutation/Adjacency.lean` or a small theorem-2 geometry companion | `2 ≤ d`, `exists_real_open_nhds_adjSwap`, a seed with fixed Euclidean time order, and large-spatial Jost geometry | an open connected real edge `V`, a time-order label `ρ`, Jost/ET/swap-ET control, and ordered-sector fields for both `x` and `x ∘ τ`; not a `d = 1` theorem |
| `swapped_support_lies_in_swapped_open_edge` | same Route-B geometry layer | the swap identity for `g` and `tsupport f ⊆ V` | support transport for `g` into the swapped open edge |
| `bvt_F_acrOne_package` | `OSToWightmanBoundaryValuesBase.lean` or a small selected-witness support file | a strengthened/refactored `full_analytic_continuation_with_symmetry_growth` theorem that retains the ACR(1) conjunct from the chosen witness | ACR(1) holomorphy, Euclidean reproduction, permutation symmetry, and translation symmetry for the selected `bvt_F OS lgc n` |
| `bvt_F_extendF_perm_eq_on_realJost_of_OS_symmetry` | `BHWExtension.lean` theorem-2 boundary layer, with OS adapters near WickRotation if cleaner | `OS.E3_symmetric`, `bvt_euclidean_restriction`, Lorentz invariance of `bvt_F`, Jost/BHW geometry, and identity/EOW propagation on the connected real Jost edge | pointwise equality of the BHW analytic continuation `extendF (bvt_F OS lgc n)` on permuted real Jost edge points |
| `BHW.HasPermutationEdgeDistributionEquality` | `BHWExtension.lean` / `BHWPermutation` support layer | a real-open Jost edge `V`, ET and permuted-ET control, and compact support of the test function | a predicate packaging permutation equality of `extendF F` as a compactly supported edge-distribution equality |
| `bvt_F_distributionalEOW_permBranch_from_euclideanEdge` | SCV/BHW theorem-2 support layer | selected `bvt_F` ACR(1) package, compact-test Euclidean edge equality, and a distributional EOW theorem | transports compact-test Euclidean branch equality to compact-test real-Jost branch equality without raw real-trace continuity |
| `bvt_F_extendF_adjacentEdgeDistribution_eq_from_OS` | WickRotation theorem-2 support layer | adjacent Euclidean order change plus `bvt_F_distributionalEOW_permBranch_from_euclideanEdge` | adjacent/order-change version of the branch distribution equality; the true local EOW seed |
| `bvt_F_extendF_perm_edgeDistribution_eq_from_OS` | WickRotation theorem-2 support layer | adjacent branch-distribution seed plus BHW/PET permutation-flow propagation, or explicit transported-overlap induction | equality of the two `extendF (bvt_F OS lgc n)` real-overlap branch pairings against compact tests for a finite permutation |
| `BHW.permuteSchwartz` and support/measure lemmas | `BHWPermutation/EdgeDistribution.lean` | implemented from coordinate permutation as a continuous linear equivalence | reusable permuted Schwartz test functions, Jost-support transport, compact-support transport, topological-support transport, and permutation-invariant integral change of variables |
| `bvt_W_perm_invariant_on_compactJostOverlap_from_OS` | WickRotation theorem-2 support layer | `bvt_F_extendF_perm_edgeDistribution_eq_from_OS`, change of variables, ET/permuted-ET support transport, and `bvt_boundary_values` | optional compatibility adapter: distributional permutation equality for `bvt_W OS lgc n` on compactly supported tests with `tsupport ⊆ V` |
| `BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality` | `BHWPermutation/EdgeDistribution.lean` | implemented from compact-test pairing equality, continuity of the two `extendF` real-edge traces, and `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` | pointwise equality of `extendF F` on any real-open Jost/permutation-overlap edge |
| `BHW.extendF_perm_eq_on_realOpen_of_jost_distribution_symmetry` | `BHWPermutation/PermutationFlow.lean` or new companion file | secondary compatibility route copying the private hLC proof spine, with `hW_overlap_perm` replacing `hF_local_dist` | same pointwise equality as the direct edge-distribution theorem; not the preferred primary route once `bvt_F_hasPermutationEdgeDistributionEquality` is available |
| `bvt_F_hasPermutationEdgeDistributionEquality` | WickRotation theorem-2 support layer | `bvt_F_extendF_perm_edgeDistribution_eq_from_OS` and the support-zero lemma outside `tsupport` | OS-side edge-distribution equality for every finite permutation, without any global `IsLocallyCommutativeWeak d (bvt_W OS lgc)` input |
| `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` | `BHWExtension.lean`, with lower helpers in `AdjacencyDistributional.lean` if needed | Route-B ET support, Euclidean/permutation symmetry, and EOW/uniqueness inputs | adjacent-only raw-boundary pairing equality without any global `IsLocallyCommutativeWeak d (bvt_W OS lgc)` input |
| `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` | `BHWExtension.lean` theorem-2 boundary-pairing layer | the adjacent-only raw-boundary supplier above | theorem-2-facing adjacent raw-boundary equality for `bvt_F`; useful edge data, not the finite-shell frontier |
| `canonical_adjacentSwap_shell_mem_EOW_domain` | BHW / adjacency geometry layer | canonical direction, `ε > 0`, adjacent spacelike support, and the Route-B overlap package | membership of the two finite canonical-shell configurations in the EOW/extended-tube domain where adjacent interchange is valid |
| `bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike` | `BHWExtension.lean` theorem-2 finite-shell layer | `bvt_F_holomorphic`, Lorentz invariance, boundary continuity, and `canonical_adjacentSwap_shell_mem_EOW_domain` | pointwise equality between the permuted-imaginary-direction shell and the canonical shell over the same real edge |
| `bvt_F_adjacentSwapCanonical_pointwise_of_spacelike` | `BHWExtension.lean` theorem-2 finite-shell layer | `swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell`, `bvt_F_perm`, and the permuted-eta finite-shell theorem | pointwise equality of the swapped-real-coordinate finite shell with the canonical shell for one adjacent spacelike pair |
| `bvt_F_adjacentSwapCanonical_pairing_from_pointwise` | `OSToWightmanBoundaryValueLimits.lean` or `OSToWightmanBoundaryValuesComparison.lean` support layer | measure-preserving coordinate reindexing, support-zero outside `tsupport f`, `hswap`, and the pointwise finite-shell theorem | adjacent canonical-shift pairing equality |
| `bvt_F_reduced` | `OSToWightmanReduced.lean` | implemented from `safeSection` and the selected OS witness | reduced-coordinate representative of `bvt_F` |
| `bvt_F_eq_bvt_F_reduced_reducedDiffMap` | `OSToWightmanReduced.lean` | implemented from `bvt_F_translationInvariant`, `reducedDiffMap_safeSection`, and `exists_uniformShift_eq_of_reducedDiffMap_eq` | pointwise factorization of `bvt_F OS lgc n z` through `reducedDiffMap n d z` |
| `canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirection` | `OSToWightmanReduced.lean` | implemented from `canonicalForwardConeDirection`, `reducedDiffMap`, and `safeBasepointVec` | reduced direction of the public canonical shell is the product-cone direction `safeBasepointVec` in every reduced slot |
| `permutedCanonicalForwardDirection_reducedDiff_eq_permOnReducedDiff` | `OSToWightmanReduced.lean` | implemented from `permOnReducedDiff_reducedDiffMap` and the previous direction lemma | reduced direction of `canonicalForwardConeDirection ∘ Equiv.swap i j` |
| `reducedPairDiff_reducedDiffMapReal` | `OSToWightmanReduced.lean` | implemented from `realDiffCoordCLE`, `prependBasepointReal`, and translation-cancellation algebra | support hypothesis `AreSpacelikeSeparated d (x i) (x j)` rewritten in reduced coordinates |
| `bvt_F_reduced_permOnReducedDiff` | `OSToWightmanReduced.lean` | implemented from reduced factorization, `permOnReducedDiff_reducedDiffMap`, and `bvt_F_perm` | reduced-coordinate permutation invariance of the descended OS-side witness |
| `permOnReducedDiff_swap_permutedCanonicalDirection` | `OSToWightmanReduced.lean` | implemented from `permOnReducedDiff_mul` and involutivity of `Equiv.swap` | selected swap sends the permuted canonical reduced direction back to the canonical reduced direction |
| `bvt_F_reduced_permutedDirection_to_realPermutedCanonical` | `OSToWightmanReduced.lean` | implemented from `bvt_F_reduced_permOnReducedDiff` | converts the permuted-imaginary-direction comparison into a canonical-direction comparison at the permuted real reduced basepoint |
| `reducedSpacelikeSwapEdge` | `OSToWightmanReduced.lean` | implemented from `reducedPairDiff` and `MinkowskiSpace.IsSpacelike` | the real reduced edge on which the selected pair is spacelike |
| `isOpen_reducedSpacelikeSwapEdge` | `OSToWightmanReduced.lean` | implemented from continuity of `reducedPairDiff` and openness of the spacelike cone | openness of the real reduced edge for local EOW neighborhoods |
| `bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge` | `OSToWightmanReduced.lean` | implemented from `bvt_F_reduced_permOnReducedDiff` | boundary equality of the two reduced branches on the spacelike real edge |
| `bvt_F_reduced_holomorphicOn_reducedForwardTube` / `bvt_F_reduced_holomorphicOn_swapPulledForwardTube` | `OSToWightmanReduced.lean` | implemented from `bvt_F_holomorphic`, `safeSection_mem_forwardTube`, and differentiability of the safe section / reduced permutation map | holomorphicity of the two reduced branches on their tube domains |
| `reduced_local_EOW_canonicalRealSwap` | reduced BHW/EOW support layer | the reduced real edge, boundary equality, branch holomorphicity, and a non-circular two-cone EOW/BHW continuation theorem | canonical-direction equality after acting on the reduced real basepoint by the selected transposition |
| `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike` | reduced finite-shell adapter layer | `reduced_local_EOW_canonicalRealSwap` | theorem-2-facing canonical real-swap equality under the pointwise spacelike hypothesis |
| `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike` | reduced finite-shell adapter layer | the three algebraic reduced-permutation lemmas and `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike` | equality between the reduced permuted-canonical-direction shell and the reduced canonical shell |
| `reducedDiffMap_canonicalShell_eq` | `OSToWightmanReduced.lean` | implemented from reduced real differences and canonical reduced direction | reduced coordinates of the canonical shell split into real reduced basepoint plus canonical imaginary direction |
| `reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq` | `OSToWightmanReduced.lean` | implemented from reduced real differences and the permuted canonical reduced direction | reduced coordinates of the permuted-eta shell split into real reduced basepoint plus permuted imaginary direction |
| `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike` | theorem-2 finite-shell layer | reduced factorization, reduced direction lemmas, `reducedPairDiff_reducedDiffMapReal`, and the reduced local-edge theorem | pointwise equality between the arbitrary-swap permuted-eta shell and the canonical shell for the same spacelike pair |
| `bvt_F_swapCanonical_pairing_from_transposition_pointwise` | `OSToWightmanBoundaryValueLimits.lean` or `OSToWightmanBoundaryValuesComparison.lean` support layer | measure-preserving coordinate reindexing, support-zero outside `tsupport f`, `hswap`, and the arbitrary-transposition pointwise finite-shell theorem | the general `swap i j` canonical pairing equality required by the frontier theorem |
| `bvt_F_swapCanonical_pairing` | `OSToWightmanBoundaryValues.lean` | only the completed arbitrary-transposition pairing theorem | final private frontier theorem consumed by `bv_local_commutativity_transfer_of_swap_pairing` |

Two negative ownership rules are part of the route contract:

1. no slot below the final frontier theorem may consume global
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)`;
2. boundary-value recovery may identify the raw boundary distribution, but it
   may not be used as if it proved equality of finite canonical-shell integrals
   for each `ε > 0`;
3. once the finite-shell pointwise theorem is closed in the BHW-extension layer,
   the pairing and general-transposition layers may not reopen BHW geometry or
   EOW arguments;
4. do not assert
   `real_spacelike_swap_edge_mem_extendedTube_overlap` in absolute coordinates:
   one selected spacelike pair does not place the whole real n-point
   configuration, or its selected transposition, in the absolute extended tube.
   The selected-pair seam belongs to reduced/local edge-of-the-wedge geometry.

## 1. The live theorem and its consumers

The live frontier theorem is:

```lean
private theorem bvt_F_swapCanonical_pairing
```

in `OSToWightmanBoundaryValues.lean`.

Its immediate consumers are:

1. `bv_local_commutativity_transfer_of_swap_pairing`
   in `OSToWightmanBoundaryValuesComparison.lean`,
2. `bvt_locally_commutative`
   in `OSToWightmanBoundaryValues.lean`,
3. the public Wightman axiom field `locally_commutative` in
   `os_to_wightman_full`.

So theorem 2 is the unique boundary-value bridge from the analytic permutation
package to the public locality axiom.

## 2. OS-paper reading of theorem 2

OS I Section 4.5 proves locality by:

1. Euclidean symmetry on the real side,
2. analytic continuation to overlapping permuted tube domains,
3. a uniqueness / edge-of-the-wedge step,
4. passage to boundary values.

This means theorem 2 belongs to the BHW / PET / Jost / edge-of-the-wedge lane.
It is not part of the theorem-3 positivity / semigroup lane.

### 2.1. OS I error / OS II correction note

The OS I / OS II correction must be kept explicit here.  The theorem-2 locality
argument may use the already-repaired many-variable analytic object `bvt_F`, but
it must not revive the broken OS I Lemma 8.8 pattern as a hidden input.

The allowed reading of OS I Section 4.5 is conceptual:

1. Euclidean symmetry supplies equality on a real edge;
2. analytic continuation and edge-of-the-wedge propagate that equality;
3. boundary values transfer the equality to the reconstructed Wightman
   functional.

The disallowed reading is:

1. assume a separate one-variable continuation can be upgraded silently to the
   joint many-variable Fourier-Laplace statement;
2. use any theorem surface that effectively presupposes global Wightman
   locality of `bvt_W OS lgc`;
3. close theorem 2 by calling a theorem whose `hLC` input is exactly
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.

## 3. Exact production hooks already available

The current code already contains the major analytic ingredients.

In `OSToWightmanBoundaryValuesBase.lean`:

1. `bvt_F_perm`
   gives permutation invariance of the analytic boundary-value continuation
   `bvt_F`.

In `BHWExtension.lean`:

1. `W_analytic_swap_boundary_pairing_eq`
   gives adjacent-swap equality of boundary pairings for compactly supported
   tests whose real support already lies in the extended tube.  It is not
   directly callable on `W := bvt_W OS lgc` in theorem 2 unless the global
   locality hypothesis is supplied non-circularly.
2. `analytic_extended_local_commutativity`
   gives pointwise adjacent-swap equality on real ET overlap points for the BHW
   extension, again with a global `IsLocallyCommutativeWeak d W` input in the
   checked theorem surface.
3. `analytic_boundary_local_commutativity_of_boundary_continuous`
   descends that pointwise equality from `BHW.extendF W_analytic` to raw
   boundary values of `W_analytic`, provided the needed boundary continuity is
   available at the two real ET points.  This theorem has the same global
   locality input and therefore belongs to the checked supplier inventory, not
   to the non-circular theorem-2 endgame by itself.
4. `W_analytic_BHW`
   packages the BHW extension used by the reverse-direction side and by any
   later uniqueness comparison.

In `AnalyticContinuation.lean` and `SCV/TubeDomainExtension.lean`:

1. `edge_of_the_wedge`
   is a proved theorem, not an axiom.
2. `SCV.edge_of_the_wedge_theorem`
   is the underlying multi-dimensional theorem.
3. `jost_lemma`
   packages the real-point spacelike geometry on the extended tube.

In `OSToWightmanBoundaryValuesComparison.lean`:

1. `bv_local_commutativity_transfer_of_swap_pairing`
   is already the public transfer theorem from the canonical BV swap pairing to
   locality of the reconstructed Wightman distribution.

So theorem 2 does not lack edge-of-the-wedge infrastructure any more. The live
gap is the last boundary-pairing adapter that feeds the existing transfer
theorem.

## 4. Honest remaining gap

The current frontier theorem asks directly for equality of the two canonical BV
pairings

```lean
∫ bvt_F(... canonical shift ...) * g
=
∫ bvt_F(... canonical shift ...) * f
```

under:

1. selected-pair spacelike separation on the support of `f`,
2. `g = f ∘ swap(i,j)`.

Older drafts said that the BHW package already proves the analogous statement
once ET-support and boundary-continuity data are supplied.  That is not precise
enough for the current tree.  The checked BHW statements do provide the correct
shape, but their theorem surfaces still include

```lean
hLC : IsLocallyCommutativeWeak d W
```

or an equivalent local-commutativity input.  For `W := bvt_W OS lgc`, that
input is circular: theorem 2 is exactly the production step meant to prove
`IsLocallyCommutativeWeak d (bvt_W OS lgc)`.

So the remaining theorem-2 task is not "prove locality from scratch," but it is
also not "instantiate the existing BHW theorem."  The honest gap is:

1. identify the exact analytic representative behind `bvt_F`;
2. prove the Route-B real-open-edge / ET-support package for the selected
   transposition `Equiv.swap i j`;
3. prove the flattened regularity and boundary-continuity package for `bvt_F`;
4. build a non-circular raw-boundary or edge-compatibility theorem whose proof
   uses Euclidean symmetry, the open-edge/EOW machinery, and boundary
   continuity, but not global locality of `bvt_W OS lgc`;
5. prove the finite canonical-shell arbitrary-transposition interchange theorem
   for each `ε > 0`; this is not a boundary-value recovery statement;
6. prove the general `swap i j` pairing adapter directly from that pointwise
   theorem.

This is the key theorem-shape correction for the next Lean stage: any proof
that closes the frontier by supplying `bvt_locally_commutative` or
`IsLocallyCommutativeWeak d (bvt_W OS lgc)` as an input has merely introduced a
cycle, not proved theorem 2.

## 5. Exact theorem-slot inventory still needed

The documentation-standard theorem slots are:

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHWCore.ExtendedTube d n) := by
  -- primary Route-B geometry package; build above
  -- `exists_real_open_nhds_adjSwap`, not by asserting global ForwardJost
  -- membership from one adjacent spacelike pair

-- Do not generalize the previous theorem by replacing the adjacent pair with
-- arbitrary `i j` and keeping the absolute ET conclusion.  That statement is
-- too strong: one selected spacelike pair does not imply absolute ET
-- membership for the whole real configuration.  The public `swap i j` theorem
-- must pass through the reduced finite-shell package below instead.

def bvt_F_reduced
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) : ReducedNPointConfig d m → ℂ :=
  fun η => bvt_F OS lgc (m + 1) (BHW.safeSection d m η)

theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    ∀ z : Fin (m + 1) → Fin (d + 1) → ℂ,
      bvt_F OS lgc (m + 1) z =
        bvt_F_reduced (d := d) OS lgc m
          (BHW.reducedDiffMap (m + 1) d z) := by
  -- global translation invariance of `bvt_F` plus the identity
  -- `safeSection (reducedDiffMap z) + constant = z`.

lemma swapped_support_lies_in_swapped_open_edge
    {V : Set (NPointDomain d n)}
    (f g : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V} := by
  -- pure support transport through the checked swap identity

lemma swapped_support_lies_in_swapped_open_edge_for_swap
    {V : Set (NPointDomain d n)}
    (f g : SchwartzNPoint d n) (i j : Fin n)
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap i j k)))
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | (fun k => x (Equiv.swap i j k)) ∈ V} := by
  -- same pure support transport, now for the selected public transposition

lemma bvt_F_boundary_continuous_at_real_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ x,
      ContinuousWithinAt
        (bvt_F OS lgc n)
        (ForwardTube d n)
        (fun k μ => (x k μ : ℂ)) := by
  -- boundary continuity of the analytic representative at the real support

lemma adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (f x) := by
  -- non-circular adjacent-only raw-boundary theorem.
  -- It may use Euclidean symmetry, EOW/uniqueness, open-edge ET data, and
  -- boundary continuity. It may not consume
  -- `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.

theorem bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (f x) := by
  -- theorem-2-facing wrapper around
  -- `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
```

The last theorem is still adjacent-only and raw-boundary-only.  The public
frontier theorem is a general transposition on the canonical imaginary cone
shift, so the downstream work is finite-shell work, not raw boundary recovery:

```lean
def canonicalShell
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def swappedCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def permutedEtaCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) +
      ε *
        ↑(canonicalForwardConeDirection
          (d := d) n (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) *
        Complex.I

lemma swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    swappedCanonicalShell (d := d) n i hi x ε =
      fun k μ =>
        permutedEtaCanonicalShell (d := d) n i hi x ε
          (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ := by
  -- ext k μ
  -- simp [swappedCanonicalShell, permutedEtaCanonicalShell, Equiv.swap_apply_self]

theorem bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) (hε : 0 < ε)
    (hsp : MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    bvt_F OS lgc n (permutedEtaCanonicalShell (d := d) n i hi x ε) =
    bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- finite-shell EOW/BHW comparison.  This is the analytic step:
  -- the two shells have the same real edge but approach it through
  -- adjacent-swapped imaginary directions.

theorem bvt_F_adjacentSwapCanonical_pointwise_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) (hε : 0 < ε)
    (hsp : MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    bvt_F OS lgc n (swappedCanonicalShell (d := d) n i hi x ε) =
    bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- Step 1: rewrite `swappedCanonicalShell` as the real-coordinate permutation
  -- of `permutedEtaCanonicalShell`.
  -- Step 2: use `bvt_F_perm` to remove that real-coordinate permutation.
  -- Step 3: apply
  -- `bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike`.
  --
  -- This finite-shell theorem is the real canonical theorem-2 bridge and is
  -- not supplied by boundary-value recovery.

theorem bvt_F_adjacentSwapCanonical_pairing_from_pointwise
    ...
```

Only after the finite-shell adjacent theorem is in place should the later file
prove the explicit reducer for a general `swap i j`.

### 5.1. Legacy/fallback strategy for the boundary-continuity slot

This subsection is retained only for the older raw-boundary / finite-height
fallback route.  It is **not** the primary OS-I theorem-2 route after the
real-Jost `extendF` correction above.  A global raw real-trace continuity theorem
for `bvt_F` is stronger than the distributional Wightman boundary-value
statement and must not be smuggled into the primary proof.

If the fallback route is deliberately retained, the continuity theorem above
should not remain a bare placeholder. There is a concrete candidate route in the
repo:

1. `ForwardTubeDistributions.lean :: boundary_function_continuous_forwardTube_of_flatRegular`
   proves continuity of the real trace of a forward-tube holomorphic function,
   provided one has a regular flattened Fourier-Laplace package
   `SCV.HasFourierLaplaceReprRegular`.
2. The later theorem-2 implementation should therefore aim first for a regular
   flattened package for `bvt_F OS lgc n`, not for pointwise continuity by raw
   epsilon-delta arguments.

For that fallback route, the theorem-slot inventory would be:

```lean
lemma bvt_F_flattened_holomorphic
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    HolomorphicOn
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.tubeDomain (ForwardConeFlat d n))

lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap)

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma flatRegular_of_boundary_distribution_and_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  exact
    flatRegular_of_boundary_distribution_and_polyGrowth
      (d := d) OS lgc n

lemma bvt_F_boundary_continuous_on_real_trace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    Continuous (fun x : NPointDomain d n => bvt_F OS lgc n (fun k μ => (x k μ : ℂ))) := by
  exact
    boundary_function_continuous_forwardTube_of_flatRegular
      (d := d) (n := n)
      (bvt_F_holomorphic OS lgc n)
      (bvt_F_hasFlatRegularRepr (d := d) OS lgc n)

lemma bvt_F_boundary_continuous_at_real_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ x,
      ContinuousWithinAt
        (bvt_F OS lgc n)
        (ForwardTube d n)
        (fun k μ => (x k μ : ℂ)) := by
  -- derive `ContinuousWithinAt` from the global real-trace continuity theorem,
  -- together with the forward-tube approach geometry at real points
```

This is a possible fallback route because it uses already-proved transport
results in `ForwardTubeDistributions.lean` rather than inventing a new local
boundary continuity argument.  It is not the current primary theorem-2 route.

If `bvt_F_hasFlatRegularRepr` turns out not to be obtainable from the current
production growth package, then that regular package is only the honest blocker
for the fallback raw-boundary route.  The primary route should instead continue
through `bvt_F_distributionalEOW_permBranch_from_euclideanEdge` and
`bvt_F_hasPermutationEdgeDistributionEquality`.

The key documentation correction is:

1. there is no current repo theorem named
   `SCV.hasFourierLaplaceReprRegular_of_boundary_and_growth`,
2. the actual missing theorem package is the constructor
   `flatRegular_of_boundary_distribution_and_polyGrowth`,
3. the later locality proof should therefore treat the regular constructor as
   the hard analytic input and the continuity theorem as a downstream consumer.

### 5.2. Fallback subpackages behind `bvt_F_hasFlatRegularRepr`

If the fallback raw-boundary route is revived, the regular flattened package
should itself be documented as a small theorem suite, not as one unexplained
miracle theorem.

The later Lean port should split it into:

```lean
lemma bvt_F_flattened_holomorphic
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    HolomorphicOn
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.tubeDomain (ForwardConeFlat d n)) := by
  -- transport `bvt_F_holomorphic` through the flattening equivalence

lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap) := by
  -- flattened form of the existing boundary-value package for `bvt_F`

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  -- transport the current growth package for `bvt_F`

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  exact
    flatRegular_of_boundary_distribution_and_polyGrowth
      (d := d) OS lgc n
```

This is the correct level of explicitness for the fallback continuity theorem
because the `ForwardTubeDistributions` package already proves the final
transport theorems.  It is not a prerequisite for the primary OS/Jost
distributional route.

The constructor theorem should be read as an actual future file target:

1. prove the flattened holomorphic theorem,
2. prove the flattened boundary-distribution theorem,
3. prove the flattened polynomial-growth theorem,
4. combine those three inputs in a new SCV/forward-tube regularity constructor,
5. only then specialize to `bvt_F_hasFlatRegularRepr`.

### 5.3. Exact route from continuity to the raw-boundary swap pairing

Once the regular flattened package is in place, the later proof should not jump
straight to the canonical shifted pairing. There is an intermediate raw-boundary
theorem surface:

```lean
theorem bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * g x
        =
      ∫ x, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * f x := by
  intro f g hf_compact hg_compact hsep hswap
  obtain ⟨V, hV_open, hf_support, hV_ET, hV_swapET⟩ :=
    choose_real_open_edge_for_adjacent_swap (d := d) (n := n) f i hi hsep
  have hg_support :=
    swapped_support_lies_in_swapped_open_edge
      (d := d) (n := n) (V := V) f g i hi hswap hf_support
  have hcont := bvt_F_boundary_continuous_at_real_support (d := d) OS lgc n
  exact
    adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility
      (d := d) (OS := OS) (lgc := lgc) n i hi f g
      hf_compact hg_compact hsep hswap
      -- the proof package supplies ET data from `hV_ET`, `hV_swapET`,
      -- `hf_support`, and `hg_support`, plus continuity from `hcont`.
```

Only after this raw-boundary theorem is in place should the later file prove
the canonical-shift adapter. That final adapter should be documented as a
separate wrapper theorem because it changes the evaluation surface from
`x ↦ x` to `x ↦ x + i ε η_can`, and that change is not part of the BHW
locality theorem itself.

### 5.4. Correct support geometry boundary

The adjacent support-to-ET package remains useful as a pilot and as context for
raw-boundary locality statements, but it is **not** the public finite-shell
transposition route.  A single selected spacelike pair does not imply that the
whole real configuration, or its selected transposition, is already in the
absolute BHW extended-tube overlap.

The adjacent pilot package therefore has these implementation targets only:

```lean
lemma choose_real_open_edge_for_adjacent_swap
lemma swapped_support_lies_in_swapped_open_edge
lemma swapped_open_edge_embeds_in_extendedTube
```

The public `swap i j` finite-shell theorem must instead pass through reduced
difference coordinates:

```lean
def bvt_F_reduced
theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
theorem reducedPairDiff_reducedDiffMapReal
theorem bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike
theorem bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike
```

`ComplexLieGroups/JostPoints.lean` remains fallback context only.  In
particular, a theorem named like
`canonical_support_mem_forwardJost_of_swap_spacelike` is not part of the
primary theorem-2 execution transcript unless it is separately proved and
recorded as a genuine geometric strengthening.  Likewise, do not introduce a
general `choose_real_open_edge_for_swap` theorem unless its statement has a new
mathematical hypothesis strong enough to imply full extended-tube membership.

### 5.5. Lean-style endgame script with all remaining theorem slots visible

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * g x
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
  intro n i j f g ε hε hsep hswap
  exact
    bvt_F_swapCanonical_pairing_from_transposition_pointwise
      (d := d) (OS := OS) (lgc := lgc) n i j f g ε hε hsep hswap
```

This is the closure standard the docs should now enforce:

1. ET support geometry named for the selected transposition,
2. boundary continuity package named,
3. non-circular raw-boundary theorem named,
4. finite-shell permuted-eta comparison named,
5. general transposition pairing adapter named.

If any one of those five is missing in a later Lean proof, then theorem 2 is
still underdocumented.

General-swap warning: any theorem named like
`bvt_F_swapCanonical_pairing_of_adjacent_chain` is not a license to bubble one
field past arbitrary intervening fields.  The live
hypothesis for `swap i j` only says that the original `i`-th and `j`-th
arguments are spacelike separated; it says nothing about the intervening
neighbors in a naive adjacent-transposition decomposition.  Therefore any
general-swap reducer is implementation-ready only after it has one of the
following exact proofs, with the direct transposition theorem as the preferred
route:

1. a direct finite-shell theorem for an arbitrary transposition `swap i j`;
2. a relabeling theorem that moves the selected pair to an adjacent pair,
   applies the adjacent theorem to that same spacelike pair, and moves back
   without changing the canonical shell statement;
3. an adjacent-chain proof whose step predicate explicitly proves that each
   adjacent step is swapping the same spacelike pair under a tracked relabeling,
   not an unrelated neighbor.

Until the direct transposition theorem or a fully tracked relabeling theorem is
written, the general-swap layer remains a proof-doc gap.

## 6. Canonical-shift adapter required by the frontier theorem

The consumer
`bv_local_commutativity_transfer_of_swap_pairing`
expects the canonical shifted pairing, not the raw real-support pairing.

Important correction: this finite-`ε` canonical shifted pairing is not obtained
by `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`.  That recovery
theorem identifies the boundary distribution/raw boundary value after taking
the boundary limit; it does not state that

```lean
∫ F(x + i ε η_can) f x = W f
```

for each fixed `ε > 0`.  The live theorem needs equality before the
`ε → 0+` limit is taken, so the canonical layer must be a finite-shell
interchange theorem.

The adjacent finite-shell package should be factored into two algebraic moves
and one analytic move.  This is important because the canonical imaginary
direction is not invariant under coordinate swaps:

1. rewrite the left shell, after changing integration variables, as a real
   coordinate permutation of a shell with the **permuted** imaginary direction;
2. use `bvt_F_perm` to remove that real coordinate permutation;
3. prove the true EOW/BHW finite-shell comparison between the permuted-eta
   shell and the canonical shell.

The implementation-ready theorem skeleton is:

```lean
def canonicalShell
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def swappedCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def permutedEtaCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) +
      ε *
        ↑(canonicalForwardConeDirection
          (d := d) n (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) *
        Complex.I

lemma swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell
    (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) (ε : ℝ) :
    swappedCanonicalShell (d := d) n i hi x ε =
      fun k μ =>
        permutedEtaCanonicalShell (d := d) n i hi x ε
          (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ := by
  ext k μ
  simp [swappedCanonicalShell, permutedEtaCanonicalShell, Equiv.swap_apply_self]

theorem bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩) →
      bvt_F OS lgc n (permutedEtaCanonicalShell (d := d) n i hi x ε) =
      bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- Genuine finite-shell EOW/BHW comparison.
  -- The two configurations have the same real edge `x`, but the imaginary
  -- direction on the left is adjacent-swapped.  This is where
  -- `canonical_adjacentSwap_shell_mem_EOW_domain`, holomorphy, boundary
  -- continuity, and uniqueness/edge-of-the-wedge are consumed.

theorem bvt_F_adjacentSwapCanonical_pointwise_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩) →
      bvt_F OS lgc n
        (fun k μ =>
          ↑(x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)
      =
      bvt_F OS lgc n
        (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) := by
  -- rewrite by `swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell`;
  -- use `bvt_F_perm` to remove the real-coordinate permutation;
  -- apply
  -- `bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike`.

theorem bvt_F_adjacentSwapCanonical_pairing_from_pointwise
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- rewrite `g` by `hswap`, change variables by the adjacent coordinate
  -- permutation, and use the pointwise finite-shell theorem on `tsupport f`;
  -- outside `tsupport f`, the integrand is zero.
```

At the current repo state, the finite-shell pointwise theorem is now isolated
as the permuted-eta comparison above, but its analytic proof transcript is not
yet complete enough for production Lean.  This remains the honest theorem-2
blocker after the first doc pass.

### 6.1. General transposition adapter, not an adjacent bubble-sort

The public frontier theorem is not adjacent-only.  Its hypothesis is:

```lean
∀ x, f.toFun x ≠ 0 →
  MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)
```

for the same selected pair `i, j` that appears in `Equiv.swap i j`.  Therefore
the final closure should use an arbitrary-transposition finite-shell theorem.
The adjacent theorem above is useful as a pilot and as the `j = i + 1` special
case, but a naive adjacent-chain decomposition is not a valid final reducer.

The general shell definitions should be:

```lean
def swappedCanonicalShellOfPerm
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x (σ k) μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I

def permutedEtaCanonicalShellOfPerm
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    ↑(x k μ) +
      ε * ↑(canonicalForwardConeDirection (d := d) n (σ k) μ) * Complex.I

lemma swappedCanonicalShellOfPerm_eq_perm_permutedEtaCanonicalShellOfPerm
    (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) (ε : ℝ)
    (hσ_inv : σ * σ = 1) :
    swappedCanonicalShellOfPerm (d := d) n σ x ε =
      fun k μ =>
        permutedEtaCanonicalShellOfPerm (d := d) n σ x ε (σ k) μ := by
  ext k μ
  have hσσ : σ (σ k) = k := by
    simpa [Equiv.Perm.mul_apply] using congr_fun hσ_inv k
  simp [swappedCanonicalShellOfPerm, permutedEtaCanonicalShellOfPerm, hσσ]
```

For the live theorem, `σ = Equiv.swap i j`, so `hσ_inv` is just
`Equiv.swap_mul_self` / `Equiv.swap_apply_self` bookkeeping.  The theorem
shape that should replace the old adjacent-chain reducer is:

```lean
theorem bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) →
      bvt_F OS lgc n
        (permutedEtaCanonicalShellOfPerm
          (d := d) n (Equiv.swap i j) x ε)
      =
      bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- arbitrary-transposition finite-shell EOW comparison.
  -- This is the non-adjacent analogue of the permuted-eta theorem above.
  -- It must not be proved by swapping unrelated adjacent neighbors.

theorem bvt_F_swapCanonical_pointwise_of_spacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) →
      bvt_F OS lgc n
        (swappedCanonicalShellOfPerm
          (d := d) n (Equiv.swap i j) x ε)
      =
      bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- rewrite the swapped shell through the permuted-eta shell;
  -- apply `bvt_F_perm` with `σ := Equiv.swap i j`;
  -- apply
  -- `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike`.

theorem bvt_F_swapCanonical_pairing_from_transposition_pointwise
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n)
      (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (f x) := by
  -- rewrite `g` using `hswap`;
  -- change variables by `Equiv.swap i j` on `NPointDomain`;
  -- the left shell becomes `swappedCanonicalShellOfPerm (Equiv.swap i j)`;
  -- use the pointwise theorem wherever `f x ≠ 0`;
  -- outside that support, both integrands vanish because of the `f x` factor.
```

This is the implementation target for the final frontier theorem.  A theorem
named `bvt_F_swapCanonical_pairing_of_adjacent_chain` should either be removed
from the production plan or renamed to a genuinely tracked relabeling theorem.
It must not mean "bubble-sort the swap through arbitrary adjacent neighbors."

### 6.2. Corrected reduced-coordinate finite-shell route

The attempted absolute theorem

```lean
real_spacelike_swap_edge_mem_extendedTube_overlap
```

must not be used.  It would say that a single selected spacelike pair forces
both `realEmbed x` and `realEmbed (x ∘ Equiv.swap i j)` into the absolute
extended tube.  That is too strong: absolute `ExtendedTube d n` is controlled by
the full successive-difference/Jost geometry, while the theorem-2 hypothesis
only controls one selected pair.

The public transposition theorem should instead reduce the finite canonical
shell to the reduced difference-coordinate seam.  The Lean packet should be:

```lean
def canonicalReducedDirection (m : ℕ) :
    Fin m → Fin (d + 1) → ℝ :=
  fun _ μ => BHW.safeBasepointVec d μ

def canonicalReducedDirectionC (m : ℕ) : ReducedNPointConfig d m :=
  fun k μ => (canonicalReducedDirection (d := d) m k μ : ℂ)

def permutedCanonicalReducedDirectionC
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) : ReducedNPointConfig d m :=
  BHW.permOnReducedDiff (d := d) (n := m + 1) σ
    (canonicalReducedDirectionC (d := d) m)

def reducedPairDiff
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) : Fin (d + 1) → ℝ :=
  fun μ =>
    ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 ξ) j μ) -
      ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 ξ) i μ)

theorem reducedPairDiff_reducedDiffMapReal
    (m : ℕ) (i j : Fin (m + 1)) (x : NPointDomain d (m + 1)) :
    reducedPairDiff (d := d) m i j
        (BHW.reducedDiffMapReal (m + 1) d x)
      =
      fun μ => x j μ - x i μ := by
  -- use `reducedDiffSection_reducedDiffMap_eq_sub_basepoint` or the real
  -- `realDiffCoordCLE`/`prependBasepointReal` identities; translations cancel.

theorem canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC
    (m : ℕ) :
    BHW.reducedDiffMap (m + 1) d
        (fun k μ => (canonicalForwardConeDirection (d := d) (m + 1) k μ : ℂ))
      =
      canonicalReducedDirectionC (d := d) m := by
  -- consecutive time labels differ by `1`, spatial labels differ by `0`.

theorem permutedCanonicalForwardDirection_reducedDiff_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    BHW.reducedDiffMap (m + 1) d
        (fun k μ => (canonicalForwardConeDirection (d := d) (m + 1) (σ k) μ : ℂ))
      =
      permutedCanonicalReducedDirectionC (d := d) m σ := by
  -- apply `permOnReducedDiff_reducedDiffMap` to the absolute canonical
  -- direction, then use
  -- `canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC`.

theorem reducedDiffMap_canonicalShell_eq
    (m : ℕ) (x : NPointDomain d (m + 1)) (ε : ℝ) :
    BHW.reducedDiffMap (m + 1) d
        (canonicalShell (d := d) (m + 1) x ε)
      =
      fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
          ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
  -- linearity of `reducedDiffMap` plus
  -- `canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC`.

theorem reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (x : NPointDomain d (m + 1)) (ε : ℝ) :
    BHW.reducedDiffMap (m + 1) d
        (permutedEtaCanonicalShellOfPerm (d := d) (m + 1) σ x ε)
      =
      fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
          ε * permutedCanonicalReducedDirectionC (d := d) m σ k μ * Complex.I := by
  -- linearity of `reducedDiffMap` plus
  -- `permutedCanonicalForwardDirection_reducedDiff_eq`.

def bvt_F_reduced
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) : ReducedNPointConfig d m → ℂ :=
  fun η => bvt_F OS lgc (m + 1) (BHW.safeSection d m η)

theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    ∀ z : Fin (m + 1) → Fin (d + 1) → ℂ,
      bvt_F OS lgc (m + 1) z =
        bvt_F_reduced (d := d) OS lgc m
          (BHW.reducedDiffMap (m + 1) d z) := by
  -- `safeSection (reducedDiffMap z)` differs from `z` by a uniform
  -- translation; apply `bvt_F_translationInvariant`.

theorem bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (m : ℕ) (i j : Fin (m + 1))
      (ξ : NPointDomain d m) (ε : ℝ), 0 < ε →
      MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) →
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)
      =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  -- This is the corrected hard analytic theorem. It is a reduced local
  -- edge-of-the-wedge statement at the selected pair. It replaces the false
  -- absolute ET-overlap claim.
```

This theorem should not be implemented monolithically.  Split off the purely
algebraic reduced-permutation part first.

```lean
theorem bvt_F_reduced_permOnReducedDiff
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ζ : ReducedNPointConfig d m) :
    bvt_F_reduced (d := d) OS lgc m
      (BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ)
    =
    bvt_F_reduced (d := d) OS lgc m ζ := by
  -- Let `zσ k := safeSection d m ζ (σ k)`.
  -- `permOnReducedDiff_reducedDiffMap` and `reducedDiffMap_safeSection`
  -- identify the reduced coordinates of `zσ`.
  -- `safeSection (permOnReducedDiff σ ζ)` and `zσ` therefore differ by a
  -- uniform complex translation; use
  -- `exists_uniformShift_eq_of_reducedDiffMap_eq` and
  -- `bvt_F_translationInvariant`.
  -- Finally use `bvt_F_perm` on `safeSection d m ζ`.

theorem permOnReducedDiff_swap_permutedCanonicalDirection
    (m : ℕ) (i j : Fin (m + 1)) :
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
      (permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j))
    =
    canonicalReducedDirectionC (d := d) m := by
  -- `permutedCanonicalReducedDirectionC` is
  -- `permOnReducedDiff (Equiv.swap i j) canonicalReducedDirectionC`;
  -- use `permOnReducedDiff_mul` and `(Equiv.swap i j) * (Equiv.swap i j) = 1`.

theorem bvt_F_reduced_permutedDirection_to_realPermutedCanonical
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) (ε : ℝ) :
    bvt_F_reduced (d := d) OS lgc m
      (fun k μ =>
        (ξ k μ : ℂ) +
          ε *
            permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
            Complex.I)
    =
    bvt_F_reduced (d := d) OS lgc m
      (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)) := by
  -- Symmetry of `bvt_F_reduced_permOnReducedDiff`.
```

After expanding the linear map in the last target and applying
`permOnReducedDiff_swap_permutedCanonicalDirection`, the hard theorem can be
rephrased in the cleaner canonical-direction form:

```lean
theorem bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (m : ℕ) (i j : Fin (m + 1))
      (ξ : NPointDomain d m) (ε : ℝ), 0 < ε →
      MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) →
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
                Complex.I))
      =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  -- After linearity and the previous direction lemma, this is the statement
  -- that the canonical-direction forward-tube value is unchanged when the
  -- real reduced basepoint is acted on by the selected transposition.
  -- This is the remaining local EOW/BHW seam.
```

The original
`bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike` should
then be a short adapter:

1. rewrite the left side by
   `bvt_F_reduced_permutedDirection_to_realPermutedCanonical`;
2. simplify the permuted direction by
   `permOnReducedDiff_swap_permutedCanonicalDirection`;
3. apply
   `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike`.

Do not use `BHW.reduced_bargmann_hall_wightman_of_input` to close this seam for
`bvt_F OS lgc`: that axiom takes a `WightmanFunctions d` input and therefore
belongs on the already-reconstructed side, where locality is part of the
structure.  The theorem-2 proof needs the OS-side `bvt_F` route, not a
post-locality Wightman bundle.

The canonical-real-swap theorem has its own proof obligations.  These are not
algebraic wrappers; they are the reduced version of the local BHW/EOW argument.

```lean
def reducedSpacelikeSwapEdge
    (m : ℕ) (i j : Fin (m + 1)) : Set (NPointDomain d m) :=
  {ξ | MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ)}

theorem isOpen_reducedSpacelikeSwapEdge
    (m : ℕ) (i j : Fin (m + 1)) :
    IsOpen (reducedSpacelikeSwapEdge (d := d) m i j) := by
  -- continuity of `reducedPairDiff` plus openness of the spacelike cone.

theorem bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    ∀ ξ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ => (ξ k μ : ℂ)))
      =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ => (ξ k μ : ℂ)) := by
  -- This boundary equality is algebraic: use
  -- `bvt_F_reduced_permOnReducedDiff`.

theorem bvt_F_reduced_holomorphicOn_reducedForwardTube
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    DifferentiableOn ℂ (bvt_F_reduced (d := d) OS lgc m)
      (BHW.ReducedForwardTubeN d m) := by
  -- compose `bvt_F_holomorphic` with `safeSection`; use
  -- `safeSection_mem_forwardTube`.

theorem bvt_F_reduced_holomorphicOn_swapPulledForwardTube
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    DifferentiableOn ℂ
      (fun ζ =>
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ))
      {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
        BHW.ReducedForwardTubeN d m} := by
  -- compose the previous holomorphicity theorem with the continuous linear map
  -- `permOnReducedDiff`.
```

The missing analytic theorem is then:

```lean
theorem reduced_local_EOW_canonicalRealSwap
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    ∀ ξ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
      ∀ ε : ℝ, 0 < ε →
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I))
        =
        bvt_F_reduced (d := d) OS lgc m
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  -- This is the true local EOW/BHW content.
  -- Inputs:
  -- 1. the two holomorphic tube branches above;
  -- 2. boundary equality on `reducedSpacelikeSwapEdge`;
  -- 3. a reduced two-cone edge-of-the-wedge / BHW continuation theorem for the
  --    cones `ReducedForwardTubeN d m` and its selected-swap pullback;
  -- 4. geometry showing the two finite shell points lie in the connected
  --    reduced EOW envelope generated by that edge.
```

This last theorem is the one remaining proof-doc gap.  The algebraic reduced
packet is ready to implement, but the production proof of theorem 2 is not
fully ready until `reduced_local_EOW_canonicalRealSwap` is expanded into a
Lean-level proof from existing SCV/BHW surfaces or into a new, non-QFT-specific
SCV theorem with a proof.

The current SCV surface must be used honestly here.  The checked theorem

```lean
SCV.edge_of_the_wedge_theorem
```

is an opposite-cone theorem for `TubeDomain C` and
`TubeDomain (Neg.neg '' C)`.  The selected-swap reduced branch naturally lives
over the pullback cone

```lean
{ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
  BHW.ReducedForwardTubeN d m}
```

which is not automatically `Neg.neg '' ReducedForwardTubeN d m`.  Therefore
the opposite-cone EOW theorem does not directly close the selected-swap seam.

There is also an endpoint issue that the proof docs must not hide.  After the
reduced permutation algebra, the genuinely hard finite-height endpoints are

```lean
def canonicalReducedShell
    (m : ℕ) (ξ : NPointDomain d m) (ε : ℝ) :
    ReducedNPointConfig d m :=
  fun k μ => (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I

def realPermutedCanonicalReducedShell
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ) :
    ReducedNPointConfig d m :=
  fun k μ =>
    (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
      (fun k μ => (ξ k μ : ℂ))) k μ
      + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I
```

and the target equality is

```lean
bvt_F_reduced (d := d) OS lgc m
  (realPermutedCanonicalReducedShell (d := d) m i j ξ ε)
=
bvt_F_reduced (d := d) OS lgc m
  (canonicalReducedShell (d := d) m ξ ε)
```

Equivalently, the left endpoint is the existing theorem statement after
expanding linearity of `permOnReducedDiff` and using
`permOnReducedDiff_swap_permutedCanonicalDirection`.  A one-variable slice that
only compares upper and lower half-planes over the same real point does not by
itself compare these two endpoints, because the real reduced basepoint has
also changed from `ξ` to `permOnReducedDiff swap ξ`.

So the next proof-doc task is one of the following, in this order of
preference:

1. prove a concrete linear-slice reduction showing that the selected
   canonical-real-swap comparison really hits both finite-height endpoints
   above and only needs an opposite-cone EOW in the one-dimensional normal
   direction to the spacelike pair;
2. otherwise prove a general two-cone EOW transport theorem in `SCV` for two
   open convex cones `C₁`, `C₂` with common real edge and a connected local
   envelope;
3. only after one of those SCV bridges exists, instantiate it for
   `ReducedForwardTubeN d m` and the selected-swap pullback cone.

Do not treat the existing opposite-cone theorem as if it directly applies to
the selected-swap cone without this reduction.

Do not treat the existing adjacent-swap EOW helpers as this bridge either.
The checked `eow_adj_swap_extension_holo_only` only places two holomorphic
branches on a union of forward-tube pieces and does not prove a connected EOW
continuation.  The checked `eow_adj_swap_on_overlap` only applies on the actual
overlap of a forward tube with its swapped copy; in the nontrivial selected
swap situation, that overlap is not the finite-height bridge required here.

The first required geometry input is therefore the connected-envelope theorem
below.  This is not enough by itself, but it records the domain membership and
connectedness that any later symmetry transport must consume.

```lean
theorem reduced_canonicalRealSwap_sameEnvelope
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (ReducedNPointConfig d m),
      IsOpen U ∧ IsPreconnected U ∧
      canonicalReducedShell (d := d) m ξ ε ∈ U ∧
      realPermutedCanonicalReducedShell (d := d) m i j ξ ε ∈ U ∧
      U ⊆
        (BHW.ReducedForwardTubeN d m) ∪
        {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
          BHW.ReducedForwardTubeN d m} ∪
        {ζ | ∃ ξ₀ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
          ζ = fun k μ => (ξ₀ k μ : ℂ)} := by
  -- Geometry of the reduced selected-pair BHW/EOW envelope.  This theorem
  -- must include the endpoint membership and connectedness needed by analytic
  -- continuation; it must not be replaced by a disconnected union statement.
```

The previous connected-envelope theorem is therefore only a geometry input, not
the analytic transport theorem.  A correct transport theorem must include a
symmetry or reflection map on the envelope and must use a real-edge identity
theorem.  The existing production theorem

```lean
SCV.identity_theorem_totally_real_product
```

is the right identity-theorem surface for this last propagation step.  The
Lean-facing transport theorem should have the following shape:

```lean
theorem reduced_connectedEnvelope_symmetry_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) (ε : ℝ)
    (U : Set (ReducedNPointConfig d m))
    (Fext : ReducedNPointConfig d m → ℂ)
    (R : ReducedNPointConfig d m → ReducedNPointConfig d m)
    (V : Set (NPointDomain d m))
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hFext_holo : DifferentiableOn ℂ Fext U)
    (hR_holo : DifferentiableOn ℂ R U)
    (hR_maps : ∀ z ∈ U, R z ∈ U)
    (hVopen : IsOpen V) (hVnonempty : V.Nonempty)
    (hVedge : V ⊆ reducedSpacelikeSwapEdge (d := d) m i j)
    (hVsubU : ∀ ξ₀ ∈ V, (fun k μ => (ξ₀ k μ : ℂ)) ∈ U)
    (hR_edge_symm :
      ∀ ξ₀ ∈ V,
        Fext (R (fun k μ => (ξ₀ k μ : ℂ))) =
        Fext (fun k μ => (ξ₀ k μ : ℂ)))
    (hR_endpoint :
      R (canonicalReducedShell (d := d) m ξ ε) =
        realPermutedCanonicalReducedShell (d := d) m i j ξ ε)
    (hcanonical_mem : canonicalReducedShell (d := d) m ξ ε ∈ U)
    (hcanonical_agree :
      Fext (canonicalReducedShell (d := d) m ξ ε) =
        bvt_F_reduced (d := d) OS lgc m
          (canonicalReducedShell (d := d) m ξ ε))
    (hrealPermuted_agree :
      Fext (realPermutedCanonicalReducedShell (d := d) m i j ξ ε) =
        bvt_F_reduced (d := d) OS lgc m
          (realPermutedCanonicalReducedShell (d := d) m i j ξ ε)) :
    bvt_F_reduced (d := d) OS lgc m
      (realPermutedCanonicalReducedShell (d := d) m i j ξ ε)
    =
    bvt_F_reduced (d := d) OS lgc m
      (canonicalReducedShell (d := d) m ξ ε) := by
  -- Apply `SCV.identity_theorem_totally_real_product` to
  -- `fun z => Fext (R z) - Fext z` on `U`.
  -- The real-open set is `V`; `hR_edge_symm` is supplied by the reduced
  -- boundary permutation equality.  Evaluate the resulting equality at
  -- `canonicalReducedShell`, rewrite with `hR_endpoint`, then use the two
  -- branch-agreement hypotheses.
```

Thus the real missing analytic/geometric theorem is not merely
`reduced_canonicalRealSwap_sameEnvelope`; it is the construction of a package

```lean
theorem exists_reduced_canonicalRealSwap_symmetricEnvelope
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (U : Set (ReducedNPointConfig d m))
      (Fext : ReducedNPointConfig d m → ℂ)
      (R : ReducedNPointConfig d m → ReducedNPointConfig d m)
      (V : Set (NPointDomain d m)),
      IsOpen U ∧ IsConnected U ∧
      DifferentiableOn ℂ Fext U ∧
      DifferentiableOn ℂ R U ∧
      (∀ z ∈ U, R z ∈ U) ∧
      IsOpen V ∧ V.Nonempty ∧
      V ⊆ reducedSpacelikeSwapEdge (d := d) m i j ∧
      (∀ ξ₀ ∈ V, (fun k μ => (ξ₀ k μ : ℂ)) ∈ U) ∧
      (∀ ξ₀ ∈ V,
        Fext (R (fun k μ => (ξ₀ k μ : ℂ))) =
        Fext (fun k μ => (ξ₀ k μ : ℂ))) ∧
      R (canonicalReducedShell (d := d) m ξ ε) =
        realPermutedCanonicalReducedShell (d := d) m i j ξ ε ∧
      canonicalReducedShell (d := d) m ξ ε ∈ U ∧
      Fext (canonicalReducedShell (d := d) m ξ ε) =
        bvt_F_reduced (d := d) OS lgc m
          (canonicalReducedShell (d := d) m ξ ε) ∧
      Fext (realPermutedCanonicalReducedShell (d := d) m i j ξ ε) =
        bvt_F_reduced (d := d) OS lgc m
          (realPermutedCanonicalReducedShell (d := d) m i j ξ ε) := by
  -- This package is the precise current proof-doc gap.  It must construct the
  -- connected EOW/BHW envelope, the continuation `Fext`, and the endpoint
  -- symmetry map `R`.  The old disconnected `FT ∪ σFT` helper does not provide
  -- these data.
```

The construction of `R` is now the named mathematical gap.  The next proof-doc
stage should not try to implement this theorem until the following subpacket is
made explicit:

```lean
def selectedSwapEnvelopeSymmetry
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ) :
    ReducedNPointConfig d m → ReducedNPointConfig d m :=
  -- To be a valid production definition, this must be an explicit affine or
  -- complex-linear map coming from the reduced BHW/Lorentz geometry, not an
  -- arbitrary function chosen only to hit the endpoint.

theorem selectedSwapEnvelopeSymmetry_maps_envelope
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) (U : Set (ReducedNPointConfig d m)) :
    ∀ z ∈ U,
      selectedSwapEnvelopeSymmetry (d := d) m i j ξ ε z ∈ U := by
  -- invariance of the constructed envelope under the selected-swap symmetry.

theorem selectedSwapEnvelopeSymmetry_holomorphic
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ)
    (U : Set (ReducedNPointConfig d m)) :
    DifferentiableOn ℂ
      (selectedSwapEnvelopeSymmetry (d := d) m i j ξ ε) U := by
  -- affine/linear maps are holomorphic; this should be a short proof once the
  -- definition is explicit.

theorem selectedSwapEnvelopeSymmetry_endpoint
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ) :
    selectedSwapEnvelopeSymmetry (d := d) m i j ξ ε
      (canonicalReducedShell (d := d) m ξ ε)
    =
      realPermutedCanonicalReducedShell (d := d) m i j ξ ε := by
  -- endpoint calculation; this is where the exact formula for `R` is checked.

theorem selectedSwapEnvelopeSymmetry_real_edge_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ)
    (Fext : ReducedNPointConfig d m → ℂ)
    (V : Set (NPointDomain d m)) :
    ∀ ξ₀ ∈ V,
      Fext
        (selectedSwapEnvelopeSymmetry (d := d) m i j ξ ε
          (fun k μ => (ξ₀ k μ : ℂ)))
      =
      Fext (fun k μ => (ξ₀ k μ : ℂ)) := by
  -- real-edge equality transferred through the reduced boundary permutation
  -- equality and the branch-agreement facts for `Fext`.
```

There is no checked production lemma yet that directly supplies this `R`.
Existing relevant surfaces are:

1. `SCV.identity_theorem_totally_real_product`, which proves propagation after
   `R`, `U`, and `Fext` are built;
2. `BHW.reduced_bargmann_hall_wightman_of_input`, which would provide reduced
   PET extension and permutation invariance for a `WightmanFunctions` input but
   is not an OS-side theorem-2 proof tool;
3. `BHW.complexLorentzAction` and reduced Lorentz equivariance of
   `reducedDiffMap`, which are likely ingredients for a non-circular
   construction of `R`;
4. the existing adjacent-swap overlap helpers, which are not enough because
   they either use a disconnected union or require actual ET-overlap already.

#### Candidate audit for the endpoint symmetry

The tempting candidates for `selectedSwapEnvelopeSymmetry` must be rejected
explicitly.  This is the current guard against reintroducing a wrapper-style
transport argument.

Use the following local notation for the selected transposition:

```lean
local notation "P" =>
  BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)

local notation "η₀" =>
  canonicalReducedDirectionC (d := d) m

local notation "ησ" =>
  permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j)

local notation "z₀" =>
  canonicalReducedShell (d := d) m ξ ε

local notation "z₁" =>
  realPermutedCanonicalReducedShell (d := d) m i j ξ ε

local notation "zσ" =>
  fun k μ => (ξ k μ : ℂ) + ε * ησ k μ * Complex.I
```

The reduced permutation algebra gives the key endpoint relation

```lean
theorem permOnReducedDiff_permutedDirection_endpoint :
    P zσ = z₁ := by
  -- This is the reduced form of permuting the real labels and the imaginary
  -- canonical direction together.
```

Consequently the analytic seam can be stated in either of two equivalent
endpoint forms:

```lean
-- canonical-real-swap form
bvt_F_reduced (d := d) OS lgc m z₁ =
  bvt_F_reduced (d := d) OS lgc m z₀

-- same-real/direction-swap form, followed by reduced permutation algebra
bvt_F_reduced (d := d) OS lgc m zσ =
  bvt_F_reduced (d := d) OS lgc m z₀
```

However, neither form is supplied by a simple global linear or affine map:

```lean
def purePermutationCandidate :
    ReducedNPointConfig d m → ReducedNPointConfig d m :=
  P

theorem purePermutationCandidate_endpoint_obstruction
    (hη : P η₀ ≠ η₀) :
    purePermutationCandidate (d := d) m i j z₀ ≠ z₁ := by
  -- Expanding `z₀` gives `P ξ + I * ε * P η₀`, while `z₁` has
  -- imaginary direction `η₀`.  Thus the pure permutation has the right
  -- real-edge action but the wrong finite-height endpoint unless the selected
  -- swap fixes the canonical reduced direction.
```

The affine correction that fixes the endpoint is

```lean
def affineEndpointCandidate
    (z : ReducedNPointConfig d m) : ReducedNPointConfig d m :=
  P z + fun k μ => ε * (η₀ k μ - (P η₀) k μ) * Complex.I
```

and it satisfies the desired endpoint calculation

```lean
theorem affineEndpointCandidate_endpoint :
    affineEndpointCandidate (d := d) m i j ξ ε z₀ = z₁ := by
  -- direct expansion
```

but it does not preserve the real edge:

```lean
theorem affineEndpointCandidate_real_edge_obstruction
    (hη : P η₀ ≠ η₀) :
    ∃ ξ₀ : NPointDomain d m,
      ¬ ∃ ξr : NPointDomain d m,
        affineEndpointCandidate (d := d) m i j ξ ε
          (fun k μ => (ξ₀ k μ : ℂ)) =
        fun k μ => (ξr k μ : ℂ) := by
  -- The imaginary translation is nonzero under `hη`; hence a real point is
  -- sent off the totally-real edge.  The real-edge boundary permutation
  -- identity therefore cannot be used to prove `Fext (R z) = Fext z` there.
```

The same obstruction appears if one instead keeps the real endpoint fixed and
tries to shift only the imaginary direction:

```lean
def sameRealDirectionCandidate
    (z : ReducedNPointConfig d m) : ReducedNPointConfig d m :=
  z + fun k μ => ε * (ησ k μ - η₀ k μ) * Complex.I

theorem sameRealDirectionCandidate_endpoint :
    sameRealDirectionCandidate (d := d) m i j ξ ε z₀ = zσ := by
  -- direct expansion

theorem sameRealDirectionCandidate_real_edge_obstruction
    (hη : ησ ≠ η₀) :
    ∃ ξ₀ : NPointDomain d m,
      ¬ ∃ ξr : NPointDomain d m,
        sameRealDirectionCandidate (d := d) m i j ξ ε
          (fun k μ => (ξ₀ k μ : ℂ)) =
        fun k μ => (ξr k μ : ℂ) := by
  -- Again the endpoint-hitting affine map translates the real edge into a
  -- finite-height imaginary slice, so it cannot be justified by the existing
  -- real-edge equality without a new finite-height theorem, which would be
  -- circular here.
```

Therefore the analytic seam is not a bookkeeping problem.  A valid proof must
produce either:

1. a genuine local BHW/Lorentz envelope symmetry whose real-edge action is a
   selected spacelike swap and whose finite-height endpoint calculation is
   `z₀ ↦ z₁`; or
2. a one-variable slice reflection theorem where the reflection lives in the
   slice parameter and the endpoint/reflection identities are proved before
   Lean implementation.

#### Route correction after the candidate audit

The audit above shows that the current private frontier theorem

```lean
bvt_F_swapCanonical_pairing
```

is a sufficient finite-height route to locality, but it is stronger than the
OS I Section 4.5 argument actually proves.  OS I uses the
Bargmann-Hall-Wightman/Jost theorem in the boundary-distribution form:

1. construct a single-valued analytic continuation on the permuted extended
   tube;
2. prove it is complex-Lorentz invariant and symmetric under permutations;
3. conclude local commutativity for the boundary distributions.

It does **not** require pointwise equality of the canonical finite-shell
integrands for every `ε > 0`.  The finite-shell target forces us to compare
`z₀` and `z₁` inside the forward/permuted tube geometry, and that is exactly
where the endpoint-symmetry obstruction appears.

So the recommended theorem-2 route should be split into two alternatives:

```lean
-- Recommended OS-I-faithful route: boundary locality directly.
theorem bv_local_commutativity_transfer_of_symmetric_PET_boundary
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (Fext : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_bv : ∀ (f : SchwartzNPoint d n)
        (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W_n f)))
    (hFext_holo : DifferentiableOn ℂ Fext (BHW.PermutedExtendedTube d n))
    (hFext_agree : ∀ z ∈ ForwardTube d n, Fext z = F z)
    (hFext_lorentz :
      ∀ (Λ : ComplexLorentzGroup d) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (BHW.complexLorentzAction Λ z) = Fext z)
    (hFext_perm :
      ∀ (σ : Equiv.Perm (Fin n)) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (fun k => z (σ k)) = Fext z) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  -- This is the Lean-facing Jost boundary theorem.  It replaces equality at
  -- every finite canonical shell by equality of the distributional boundary
  -- values obtained from the symmetric PET continuation.
```

For the OS-side witness this should be fed by a non-circular PET-extension
theorem:

```lean
theorem bvt_F_symmetric_PET_extension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ Fext : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fext (BHW.PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, Fext z = bvt_F OS lgc n z) ∧
      (∀ (Λ : ComplexLorentzGroup d) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (BHW.complexLorentzAction Λ z) = Fext z) ∧
      (∀ (σ : Equiv.Perm (Fin n)) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (fun k => z (σ k)) = Fext z) := by
  -- OS I Section 4.5 BHW extension stage for the already-constructed OS-side
  -- analytic witness `bvt_F`.  This theorem must use Euclidean symmetry,
  -- translation invariance, and the Lorentz covariance package already proved
  -- for `bvt_F`; it must not consume `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.
```

This theorem is not supplied by the checked production theorem

```lean
BHW.bargmann_hall_wightman_theorem
```

because that theorem currently takes

```lean
hF_local_dist : IsLocallyCommutativeWeak d W
```

as an input.  For theorem 2 with `W := bvt_W OS lgc`, that input is the target
conclusion and is therefore circular.  The primary route needs a sibling BHW
theorem whose matching datum is Euclidean/permutation symmetry of the OS-side
analytic continuation, not Wightman local commutativity.

There is already an important production hook for the primary route.  In
`Connectedness/BHWPermutation/PermutationFlow.lean`, the private theorem

```lean
iterated_eow_permutation_extension_of_extendF_perm
```

shows that the right non-circular input is not global Wightman locality.  It is
the extended-tube overlap equality

```lean
∀ z, z ∈ ExtendedTube d n →
  permAct (d := d) σ z ∈ ExtendedTube d n →
  extendF F (permAct (d := d) σ z) = extendF F z
```

for each permutation `σ`.  This is exactly the seam where the existing BHW
theorem currently obtains equality from `IsLocallyCommutativeWeak d W`.  The
OS-side theorem-2 route should expose this overlap-equality spine publicly and
prove it from Euclidean/permutation symmetry of the OS boundary data.

Do not replace this seam by the private theorem

```lean
extendF_perm_overlap_from_forwardTube_permInvariance
```

unless its strong input has actually been proved.  Its hypothesis is not the
same as the checked `bvt_F_perm`: it asks for

```lean
F (Γ • (w ∘ σ)) = F w
```

whenever `w ∈ ForwardTube` and `Γ • (w ∘ σ) ∈ ForwardTube`.  Plain global
coordinate-permutation invariance of `bvt_F` does not give this, because the
intermediate point `Γ • w` need not be in the forward tube.  This is precisely
the BHW/Jost continuation content.

The generic BHW theorem needed for the primary route should therefore have this
shape:

```lean
theorem bargmann_hall_wightman_theorem_of_extendF_perm
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hExtPerm :
      ∀ (σ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.ExtendedTube d n →
        BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n →
        BHW.extendF F (BHW.permAct (d := d) σ z) =
          BHW.extendF F z) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (BHW.PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      (∀ (Λ : ComplexLorentzGroup d) z,
        z ∈ BHW.PermutedExtendedTube d n →
        F_ext (BHW.complexLorentzAction Λ z) = F_ext z) ∧
      (∀ (σ : Equiv.Perm (Fin n)) z,
        z ∈ BHW.PermutedExtendedTube d n →
        F_ext (fun k => z (σ k)) = F_ext z) ∧
      (∀ (G : (Fin n → Fin (d + 1) → ℂ) → ℂ),
        DifferentiableOn ℂ G (BHW.PermutedExtendedTube d n) →
        (∀ z ∈ ForwardTube d n, G z = F z) →
        ∀ z ∈ BHW.PermutedExtendedTube d n, G z = F_ext z) := by
  -- Same output as the existing BHW theorem, but with the non-circular
  -- `extendF` overlap-invariance input replacing `hF_local_dist`.
```

The overlap-invariance input should be supplied by a smaller real-open-edge
package.  The named package must be a concrete distributional branch equality,
not an abstract proposition with no content:

```lean
def BHW.HasPermutationEdgeDistributionEquality
    (d n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (V : Set (NPointDomain d n)),
    IsOpen V →
    (∀ x ∈ V, x ∈ BHW.JostSet d n) →
    (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) →
    (∀ x ∈ V,
      BHW.realEmbed (fun k => x (σ k)) ∈ BHWCore.ExtendedTube d n) →
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      ∫ x : NPointDomain d n,
        (BHW.extendF F
            (BHW.realEmbed (fun k => x (σ k))) -
          BHW.extendF F (BHW.realEmbed x)) * φ x
      = 0
```

From this package, the production theorem should follow the same structure as
the current private hLC-based proof, with the hLC-dependent step replaced by
the OS-side edge equality:

```lean
theorem BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (hEdge :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
          =
          ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed x) * φ x) :
    ∀ x ∈ V,
      BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) =
        BHW.extendF F (BHW.realEmbed x) := by
  -- implemented in `BHWPermutation/EdgeDistribution.lean`.
  -- This is the direct compact-test pairing form consumed by the SCV theorem.

theorem BHW.extendF_perm_overlap_of_edgePairingEquality
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (hOverlap_conn :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
          BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n})
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V) (hV_ne : V.Nonempty)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (hEdge :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
          =
          ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed x) * φ x) :
    ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ BHW.ExtendedTube d n →
      BHW.permAct (d := d) σ z ∈ BHW.ExtendedTube d n →
      BHW.extendF F (BHW.permAct (d := d) σ z) =
        BHW.extendF F z := by
  -- implemented in `BHWPermutation/EdgeDistribution.lean`.
  -- It applies `BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality`
  -- on `V`, then uses `extendF_perm_eq_on_connectedDomain_of_realOpen`
  -- on the explicit connected overlap.
```

For `F := bvt_F OS lgc n`, the concrete theorem slot is:

```lean
theorem bvt_F_restrictedLorentzInvariant_forwardTube
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      bvt_F OS lgc n
        (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
      bvt_F OS lgc n z := by
  -- implemented in `OSToWightmanSelectedWitness.lean` from
  -- `BHW.Task5Bridge.real_lorentz_invariance_from_euclidean_distributional`
  -- and `bvt_F_ofEuclidean_wick_pairing`.

theorem bvt_F_complexLorentzInvariant_forwardTube
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (Λ : ComplexLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n →
      BHW.complexLorentzAction Λ z ∈ ForwardTube d n →
      bvt_F OS lgc n (BHW.complexLorentzAction Λ z) =
        bvt_F OS lgc n z := by
  -- implemented in `OSToWightmanSelectedWitness.lean` from
  -- `BHW.complex_lorentz_invariance` and the restricted real theorem above,
  -- with the `BHW.ForwardTube`/root `ForwardTube` adapter made explicit.

theorem bvt_F_extendF_perm_eq_on_realJost_of_OS_symmetry
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ σ : Equiv.Perm (Fin n),
      ∀ x : NPointDomain d n,
        x ∈ BHW.JostSet d n →
        BHW.realEmbed x ∈ BHW.ExtendedTube d n →
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n →
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (σ k))) =
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  -- This is the OS-side Jost theorem replacing the hLC-based real-open
  -- equality currently used inside `PermutationFlow.lean`.
  --
  -- It must not be proved by asserting global continuity of the raw real trace
  -- `x ↦ bvt_F OS lgc n (realEmbed x)`: Wightman boundary values are
  -- distributional in general.  The equality is instead an equality of the
  -- BHW analytic continuation `extendF` on real Jost points.
  --
  -- Proof inputs:
  -- 1. Euclidean permutation symmetry `OS.E3_symmetric`;
  -- 2. the Euclidean restriction theorem for `bvt_F`;
  -- 3. `bvt_F_restrictedLorentzInvariant_forwardTube` and the derived complex
  --    Lorentz invariance;
  -- 4. Jost/BHW geometry identifying real Jost points as real edges of the
  --    extended tube;
  -- 5. the identity theorem / edge-of-the-wedge propagation on the connected
  --    real Jost edge.

theorem bvt_F_hasPermutationEdgeDistributionEquality
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ σ : Equiv.Perm (Fin n),
      BHW.HasPermutationEdgeDistributionEquality d n (bvt_F OS lgc n) σ := by
  intro σ V hV_open hV_jost hV_ET hV_permET φ hφ_compact hφ_supp
  have hpoint :=
    bvt_F_extendF_perm_eq_on_realJost_of_OS_symmetry
      (d := d) OS lgc n σ
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hxV : x ∈ V
  · have hx_eq := hpoint x (hV_jost x hxV) (hV_ET x hxV) (hV_permET x hxV)
    simp [hx_eq]
  · have hφ_zero : φ x = 0 := by
      -- `hφ_supp` says `tsupport φ ⊆ V`; outside `V`, the value is zero.
      have hx_not_tsupport : x ∉ tsupport (φ : NPointDomain d n → ℂ) := by
        intro hx
        exact hxV (hφ_supp hx)
      exact image_eq_zero_of_notMem_tsupport hx_not_tsupport
    simp [hφ_zero]
```

For `F := bvt_F OS lgc n`, this boundary equality should be proved from:

1. the OS Euclidean permutation axiom `OS.E3_symmetric`;
2. `bvt_euclidean_restriction`, identifying the Euclidean real section of the
   analytic witness with the OS Schwinger functional;
3. `bvt_F_restrictedLorentzInvariant_forwardTube` and
   `bvt_F_complexLorentzInvariant_forwardTube`;
4. Jost/BHW real-edge geometry and the connected-domain identity theorem;
5. the elementary support lemma that a Schwartz function vanishes outside its
   topological support.

Global `bvt_F_perm` is useful context, but it is not by itself the proof of PET
symmetry: `extendF` is defined by choosing forward-tube representatives, and a
permuted real Jost point may have a different representative.  The primary
edge theorem must compare the BHW continuation values themselves.

#### The exact OS replacement for the forbidden hLC step

The current private proof
`extendF_perm_eq_on_realOpen_of_distributional_local_commutativity` should be
mined very literally.  Its analytic and measure-theoretic spine is usable:

1. define the two continuous real-edge traces
   `gV x := extendF F (realEmbed (x ∘ σ))` and
   `hVf x := extendF F (realEmbed x)`;
2. use `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`;
3. recover both integrals as boundary values of the same forward-tube witness;
4. reduce the equality of those two integrals to a distributional permutation
   equality for the boundary distribution on Jost-supported test functions.

The only circular line in that private proof is:

```lean
have hW_eq : W n φσ = W n φ :=
  distributional_perm_invariant_on_jost_support (d := d) n W hF_local_dist
    φ hφ_jost σ⁻¹
```

For theorem 2 this must be replaced by the OS theorem:

```lean
theorem bvt_W_perm_invariant_on_compactJostOverlap_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (σ : Equiv.Perm (Fin n))
      (V : Set (NPointDomain d n)),
      IsOpen V →
      (∀ x ∈ V, x ∈ BHW.JostSet d n) →
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) →
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) →
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      bvt_W OS lgc n
        (BHW.permuteSchwartz (d := d) σ⁻¹ φ) =
      bvt_W OS lgc n φ := by
  -- Compatibility adapter, not the theorem-2 OS core:
  -- the direct branch-distribution theorem plus boundary recovery implies that
  -- the reconstructed Wightman boundary distribution has permutation-equal
  -- values on compact tests supported in the chosen Jost overlap `V`.
```

The local-overlap, compact-support, and topological-support hypotheses are
deliberate.  The existing open-real-edge
uniqueness theorem
`SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` only
tests compactly supported Schwartz functions with `tsupport` in the chosen real
open set `V`.  Proving permutation equality for all Jost-supported Schwartz
functions would be stronger than the current BHW/PET spine needs and should not
be made a blocker for theorem 2.  Requiring `tsupport φ ⊆ V` is also the
OS-correct condition: since `V ⊆ JostSet`, it lets the Euclidean test be
regarded as a `ZeroDiagonalSchwartz` test by separating its topological support
from the coincidence locus.  A pointwise nonzero-support condition is enough
for the old hLC proof, but it is too weak for the OS axiom surface.

The existing private `permuteSchwartz` construction from `PermutationFlow.lean`
must be publicized with its support, compact-support, and measure-preserving
lemmas:

```lean
def BHW.permuteSchwartz
    (σ : Equiv.Perm (Fin n)) (φ : SchwartzNPoint d n) :
    SchwartzNPoint d n := ...

@[simp] theorem BHW.permuteSchwartz_apply ...
@[simp] theorem BHW.permuteSchwartz_mul ...
theorem BHW.permute_support_jost ...
theorem BHW.permute_tsupport_jost ...
theorem BHW.permuteSchwartz_hasCompactSupport ...
theorem BHW.integral_perm_eq_self ...
```

With the direct edge-distribution package available, the preferred
Lean-facing pointwise theorem should not pass through `W` at all.  It is just
the compact-support uniqueness theorem applied to the two continuous
`extendF` traces:

```lean
theorem BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (hEdge :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
          =
          ∫ x : NPointDomain d n,
            BHW.extendF F (BHW.realEmbed x) * φ x) :
    ∀ x ∈ V,
      BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) =
        BHW.extendF F (BHW.realEmbed x) := by
  -- Define `gV x := extendF F (realEmbed (x ∘ σ))` and
  -- `hVf x := extendF F (realEmbed x)`.
  -- Use `extendF_holomorphicOn` to get continuity of both traces on `V`.
  -- Apply
  -- `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`.
  -- In the test-function callback, pass
  -- `hEdge φ hφ_compact hφ_tsupport` directly.
```

This theorem is implemented and exact-checked in
`BHWPermutation/EdgeDistribution.lean`.  The zero-of-difference formulation of
edge distribution equality remains useful as an OS-side mathematical package,
but the Lean-facing uniqueness theorem consumes pairing equality directly,
which avoids smuggling an extra integrability obligation into this adapter.

The theorem below is a secondary compatibility route, useful only if we decide
to mine the private hLC proof literally.  It should not be the primary route
once `bvt_F_hasPermutationEdgeDistributionEquality` has been proved.

```lean
theorem BHW.extendF_perm_eq_on_realOpen_of_jost_distribution_symmetry
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hF_bv_dist :
      ∀ (φ : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W n φ)))
    (hW_overlap_perm :
      ∀ (σ : Equiv.Perm (Fin n))
        (V : Set (NPointDomain d n)),
        IsOpen V →
        (∀ x ∈ V, x ∈ BHW.JostSet d n) →
        (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) →
        (∀ x ∈ V,
          BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) →
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        W n (BHW.permuteSchwartz (d := d) σ⁻¹ φ) = W n φ)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) :
    ∀ x ∈ V,
      BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) =
        BHW.extendF F (BHW.realEmbed x) := by
  -- Copy the private proof, replacing the hLC-derived `hW_eq` with
  -- `hW_overlap_perm σ V hV_open hV_jost hV_ET hV_permET
  --   φ hφ_compact hφ_tsupport`.
```

Then the OS specialization is:

```lean
theorem bvt_F_extendF_perm_eq_on_realJost_of_OS_symmetry
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ σ x,
      x ∈ BHW.JostSet d n →
      BHW.realEmbed x ∈ BHW.ExtendedTube d n →
      BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n →
      BHW.extendF (bvt_F OS lgc n)
        (BHW.realEmbed (fun k => x (σ k))) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) := by
  -- Apply the generic real-open theorem on the open set
  -- `{y | y ∈ JostSet d n ∧ realEmbed y ∈ ET ∧ realEmbed (y∘σ) ∈ ET}`
  -- or on a smaller neighborhood supplied by the caller.
  -- Inputs:
  --   hF_holo      := bvt_F_holomorphic OS lgc n
  --   hF_lorentz   := bvt_F_restrictedLorentzInvariant_forwardTube OS lgc n
  --   hEdge        := bvt_F_hasPermutationEdgeDistributionEquality OS lgc n σ V ...
```

This decomposition is the current proof-doc frontier.  The generic
`extendF`/Schwartz/support code is close to implementation because it is already
present privately.  The genuinely mathematical theorem still requiring proof
documentation is `bvt_F_extendF_perm_edgeDistribution_eq_from_OS`.

That theorem must be proved by an OS/BHW edge argument, not by raw continuity
and not by first proving global Wightman locality:

1. construct the OS-side analytic branches for the two permutation orderings
   from the ACR(1) witness behind `bvt_F`;
2. prove their Euclidean restrictions agree by `OS.E3_symmetric` and
   `bvt_euclidean_restriction`;
3. use the repaired many-variable identity/EOW theorem on the Jost real edge;
4. identify the resulting real-edge distribution with the two
   `extendF (bvt_F OS lgc n)` boundary traces on the chosen overlap `V`.

Until this four-step OS edge theorem is written at this level of precision, the
production Lean proof should stop before `bvt_F_extendF_perm_eq_on_realJost...`.

#### Selected-witness issue for the OS edge theorem

The selected-witness ACR package is now implemented.  The current definition

```lean
def bvt_F (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (full_analytic_continuation_with_acr_symmetry_growth OS lgc n).choose
```

keeps the theorem-2 proof about the same selected analytic object used by all
downstream boundary-value theorems and avoids any transfer theorem between
independent `Classical.choose` witnesses.  The implemented theorem surface is:

```lean
theorem full_analytic_continuation_with_acr_symmetry_growth
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (AnalyticContinuationRegion d k 1) ∧
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) ∧
      (∀ (σ : Equiv.Perm (Fin k)) (z : Fin k → Fin (d + 1) → ℂ),
        W_analytic (fun j => z (σ j)) = W_analytic z) ∧
      (∀ (z : Fin k → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        W_analytic (fun j => z j + a) = W_analytic z) ∧
      (∀ (x : NPointDomain d k) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (W_analytic (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        W_analytic (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ ForwardTube d k,
          ‖W_analytic z‖ ≤ C_bd * (1 + ‖z‖) ^ N
```

It is proved by reusing the already-checked
`schwinger_continuation_base_step_acrOne_assembly_with_translationInvariant`;
the `ForwardTube` holomorphy conjunct is just `hACR.mono
(forwardTube_subset_acr_one ...)`, and the growth conjunct is the existing
ACR(1) growth restricted to `ForwardTube`.

The selected `bvt_F` API now exposes:

```lean
theorem bvt_F_acrOne_package ...
```

by projection from the stronger `choose_spec`.

#### Local-overlap decomposition of the OS branch equality

The OS distribution theorem needed by the public real-open `extendF` theorem is
not a global all-Jost statement and does not need to be routed through `bvt_W`
first.  The preferred object is the compact edge-distribution equality for the
two `extendF` real-edge traces on the same real-open overlap `V`.

Important implementation guardrail: the theorem below is an exported package
for an arbitrary permutation `σ`; it is not meant to be proved by a single
ACR(1) edge-of-the-wedge application for arbitrary `σ`.  The local EOW seed is
the adjacent/order-change statement.  The arbitrary-permutation export must be
obtained either by the BHW/PET permutation-flow machinery or by an explicit
transported-overlap induction that supplies every intermediate ET/permuted-ET
overlap.  Do not hide that propagation inside the name below.

```lean
theorem bvt_F_extendF_perm_edgeDistribution_eq_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (σ k))) * φ x
      =
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- Export theorem.  The proof must factor through the adjacent/order-change
  -- OS EOW seed plus BHW/PET propagation, or through an explicit transported
  -- overlap induction.  It is not a one-shot ACR(1) theorem for arbitrary σ.
```

The adjacent seed is the actual local EOW theorem:

```lean
theorem bvt_F_extendF_adjacentEdgeDistribution_eq_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_swapET :
      ∀ x ∈ V,
        BHW.realEmbed
          (fun k => x ((Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈
            BHW.ExtendedTube d n)
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed
            (fun k => x ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) * φ x
      =
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- OS.E3_symmetric gives equality on the Euclidean edge.
  -- The selected ACR(1) branch package and many-variable EOW propagate that
  -- equality to the adjacent real-open Jost overlap `V`.
```

The analytic theorem hidden in the last comment must be stated separately.  The
checked theorem

```lean
SCV.edge_of_the_wedge_theorem
```

has pointwise continuous boundary hypotheses.  The OS input supplied by
`OS.E3_symmetric` and `bvt_euclidean_restriction` is instead a compact-test
distributional equality on the Euclidean edge.  Therefore the production proof
needs a distributional EOW bridge, not a call to the pointwise theorem with an
unstated raw boundary-continuity assumption:

```lean
theorem bvt_F_distributionalEOW_permBranch_from_euclideanEdge
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (hEuclid :
      ∀ (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x (σ k))) * φ x
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x) :
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (σ k))) * φ x
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- This is the honest analytic seam.  It should be proved as a compact-test
  -- distributional EOW statement for the selected `bvt_F_acrOne_package`.
  -- It must not assert pointwise continuity of
  -- `x ↦ bvt_F OS lgc n (BHW.realEmbed x)`.
```

This theorem is allowed to be an SCV/BHW support theorem if stated without QFT
objects, but if it mentions `OS`, `bvt_F`, or `bvt_W`, it belongs in the
Wick-rotation theorem-2 support layer.  In either placement, it is the remaining
mathematical proof-doc gap for the branch-distribution route.

The implementation-ready decomposition is the following.  The local version of
the already-checked Wick-section identity theorem has now been added in
`OSToWightmanTubeIdentity.lean`.  The older theorem
`eqOn_openConnected_of_distributional_wickSection_eq` asks for compact-test
equality on the full Wick section of `U`; the theorem-2 route only has equality
on a chosen real-open overlap `V`.  The needed general SCV lemma is:

```lean
theorem eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen
    (U : Set (Fin n → Fin (d + 1) → ℂ))
    (V : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_wick :
      ∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U)
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F U)
    (hG : DifferentiableOn ℂ G U)
    (hint :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
        ∫ x : NPointDomain d n,
            F (fun k => wickRotatePoint (x k)) * φ x =
        ∫ x : NPointDomain d n,
            G (fun k => wickRotatePoint (x k)) * φ x) :
    Set.EqOn F G U := by
  -- Copy the proof of
  -- `eqOn_openConnected_of_distributional_wickSection_eq`.
  -- The only change is that the preliminary real equality is obtained on
  -- `V`, not on the whole Wick section of `U`:
  --
  --   1. use continuity of the Wick traces on `V`;
  --   2. apply
  --      `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`
  --      with `hV_open` and `hint`;
  --   3. apply `SCV.identity_theorem_totally_real_product` to the holomorphic
  --      difference on the connected domain `U`, with the nonempty open real
  --      edge `V`.
```

If `V = ∅`, the branch-distribution theorem should bypass this identity theorem:
`tsupport φ ⊆ ∅` implies the test is zero, so both integrals vanish.  All
nontrivial applications to pointwise real-open equality use neighborhoods of a
chosen point and therefore have `V.Nonempty`.

Second, isolate the genuine BHW/PET analytic continuation data as an envelope
theorem.  This theorem is not a wrapper: it is exactly the missing statement
that the two branches have a common connected holomorphic domain joining the
Euclidean Wick edge to the real Jost overlap.

Important correction: this envelope is sector-local on the Euclidean side.
For a general real-open Jost overlap `V`, the Wick-rotated points
`fun k => wickRotatePoint (x k)` need not lie in `ACR(1)` or in the forward
tube.  The ACR(1) witness is holomorphic on the ordered Euclidean time sector;
outside that sector its values are still defined as a total function, but they
cannot be used as boundary values of a holomorphic branch without first
permuting to an ordered sector.  Therefore the implementation must prove the
branch envelope in the following order:

1. Sector-local envelope for a fixed strict Euclidean time ordering `τ`.
2. Distributional EOW on that sector.
3. Finite sector decomposition / partition of the compact test pairing,
   using permutation symmetry to rewrite each sector back to the original
   branch.
4. A separate null-wall lemma for the time-tie hyperplanes, or a smooth
   partition-of-unity construction that avoids non-Schwartz indicator
   functions.

The theorem name below is the exported all-`V` package.  Its proof must not
pretend that the all-`V` Euclidean edge is a single ACR(1) edge.

```lean
theorem bvt_F_permBranchEnvelope_on_jostOverlap_from_ACR_and_BHW
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
      (F_id F_perm : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U ∧
      IsConnected U ∧
      (∀ x ∈ V, (fun k => wickRotatePoint (x k)) ∈ U) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
      DifferentiableOn ℂ F_id U ∧
      DifferentiableOn ℂ F_perm U ∧
      (∀ x ∈ V,
        F_id (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
      (∀ x ∈ V,
        F_perm (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (σ k)))) ∧
      (∀ x ∈ V,
        F_id (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) ∧
      (∀ x ∈ V,
        F_perm (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (σ k)))) := by
  -- This is the analytic/PET seam.  The proof should use:
  --   * `bvt_F_acrOne_package` for the selected witness on the Euclidean side;
  --   * the checked BHW `extendF` holomorphy on the extended tube;
  --   * Jost/ET geometry for `V`;
  --   * adjacent/order-change EOW plus permutation-flow propagation for
  --     arbitrary `σ`.
  --
  -- Do not prove the arbitrary-`σ` envelope by a one-shot ACR(1) argument.
  -- The adjacent envelope is the local seed; the arbitrary envelope is an
  -- export of the BHW/PET permutation-flow spine.
```

The sector-local statement should be explicit:

```lean
def EuclideanOrderedPositiveTimeSector
    (τ : Equiv.Perm (Fin n)) : Set (NPointDomain d n) :=
  {x | (fun k => x (τ k)) ∈ OrderedPositiveTimeRegion d n}

theorem wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
    (τ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx : x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ) :
    (fun k => wickRotatePoint (x (τ k))) ∈ ForwardTube d n := by
  -- Apply `euclidean_ordered_in_forwardTube` to the permuted Euclidean
  -- configuration.  The positivity condition is essential because the
  -- absolute-coordinate forward tube compares the first point with the origin.

theorem bvt_F_permBranchEnvelope_on_timeSector_from_ACR_and_BHW
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ τ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_sector : V ⊆ EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) :
    ∃ (U : Set (Fin n → Fin (d + 1) → ℂ))
      (F_id F_perm : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      IsOpen U ∧
      IsConnected U ∧
      (∀ x ∈ V, (fun k => wickRotatePoint (x (τ k))) ∈ U) ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ U) ∧
      DifferentiableOn ℂ F_id U ∧
      DifferentiableOn ℂ F_perm U ∧
      (∀ x ∈ V,
        F_id (fun k => wickRotatePoint (x (τ k))) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
      (∀ x ∈ V,
        F_perm (fun k => wickRotatePoint (x (τ k))) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (σ k)))) ∧
      (∀ x ∈ V,
        F_id (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) ∧
      (∀ x ∈ V,
        F_perm (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (σ k)))) := by
  -- Use `bvt_F_acrOne_package` and
  -- `wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector` to place the Wick edge
  -- on an honest holomorphic branch.  The equations on the Wick edge use
  -- `bvt_F_perm` to remove the sector-ordering permutation `τ`.  For the
  -- permuted branch, the relevant forward-tube permutation is
  -- `ρ := τ⁻¹ * σ`, since
  -- `(fun k => wickRotatePoint (x (τ k))) ∘ ρ =
  --   fun k => wickRotatePoint (x (σ k))`.
  -- The real-edge equations use BHW `extendF`.
```

This correction also changes the all-sector export.  The old phrase "strict
time sector decomposition" is not implementation-ready by itself for two
separate reasons:

1. ordering alone does not put the Wick point in the absolute-coordinate
   forward tube; positive time is needed for the first point relative to the
   origin;
2. an arbitrary compactly supported Euclidean test is not supported in the
   positive-time cone.

The production-ready export should use a **uniform translation of the compact
support**, not a pointwise translation depending on `x`.  This keeps the
Schwartz-test surface honest.  Given a compactly supported test `φ`, choose one
real Euclidean time shift `A` so that every point in `tsupport φ` has positive
time after adding `A` to the time coordinate.  Then work with the translated
test and translate the resulting real-edge equality back by real translation
invariance.

The support and null-wall lemmas needed for this are:

```lean
theorem ae_pairwise_distinct_timeCoords :
    ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0

def positiveTimeTranslate (A : ℝ) (x : NPointDomain d n) :
    NPointDomain d n :=
  fun k μ => x k μ + if μ = 0 then A else 0

theorem exists_uniform_positiveTimeShift_of_compact_tsupport
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ),
        ∀ k : Fin n, 0 < positiveTimeTranslate (d := d) (n := n) A x k 0

theorem positiveTimeTranslate_mem_orderedSector_of_pairwise_distinct
    (A : ℝ) (hApos :
      ∀ k : Fin n, 0 < positiveTimeTranslate (d := d) (n := n) A x k 0)
    (hdistinct : ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0) :
    ∃ τ : Equiv.Perm (Fin n),
      positiveTimeTranslate (d := d) (n := n) A x ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n) τ
```

For the compact-support shift, use compactness of `tsupport φ` and continuity
of the finitely many coordinate functions `x ↦ x k 0` to get a lower bound.
For the sector theorem, use `τ := Tuple.sort (fun k => x k 0)`; pairwise
distinctness upgrades monotone sorting to strict monotonicity, and the uniform
positivity hypothesis gives the positive-time part.

The theorem-2 use of this shift is only branch placement.  It must not replace
the OS-side Euclidean equality with a Wightman-side permutation theorem.  The
actual equality still comes from

```lean
OS.E3_symmetric
bvt_euclidean_restriction
bvt_F_translationInvariant
bvt_F_perm
```

The translated-test surface should be explicit.  If `a_A` is the real
spacetime vector with time component `A` and spatial components `0`, then
`positiveTimeTranslate A x = fun k => x k + a_A`.  The existing semigroup
test map is exactly the required translated test:

```lean
timeShiftSchwartzNPoint (d := d) A φ
```

and prove:

```lean
@[simp] theorem timeShiftSchwartzNPoint_apply_positiveTimeTranslate
    (A : ℝ) (φ : SchwartzNPoint d n) (y : NPointDomain d n) :
    timeShiftSchwartzNPoint (d := d) A φ y =
      φ (positiveTimeTranslate (d := d) (n := n) (-A) y)

theorem hasCompactSupport_timeShiftSchwartzNPoint
    (A : ℝ) (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ)) :
    HasCompactSupport
      (timeShiftSchwartzNPoint (d := d) A φ :
        NPointDomain d n → ℂ)

theorem tsupport_timeShiftSchwartzNPoint_subset_positiveTimeTranslate_image
    (A : ℝ) (φ : SchwartzNPoint d n)
    (V : Set (NPointDomain d n))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    tsupport
        (timeShiftSchwartzNPoint (d := d) A φ :
          NPointDomain d n → ℂ)
      ⊆ positiveTimeTranslate (d := d) (n := n) A '' V
```

The real-open image data can be transported by the same real translation:

```lean
theorem isOpen_positiveTimeTranslate_image
    (A : ℝ) (V : Set (NPointDomain d n)) (hV_open : IsOpen V) :
    IsOpen (positiveTimeTranslate (d := d) (n := n) A '' V)
```

However, the following tempting theorem shapes are **false** for the current
absolute-coordinate BHW definitions and must not be implemented:

```lean
-- false
positiveTimeTranslate A x ∈ BHW.JostSet d n ↔ x ∈ BHW.JostSet d n

-- false
BHW.realEmbed (positiveTimeTranslate A x) ∈ BHW.ExtendedTube d n ↔
  BHW.realEmbed x ∈ BHW.ExtendedTube d n
```

Reason: `BHW.JostSet d n` is not only a pairwise-difference condition; by
definition it also requires every absolute point `x i` to be spacelike relative
to the origin.  Uniform time translation preserves pairwise differences but can
turn an individual spacelike vector into a timelike vector.  The
absolute-coordinate `ExtendedTube` has the same issue: translation invariance of
the **value** of the BHW extension is available only under explicit hypotheses
that both configurations already lie in `PermutedExtendedTube`, not as
membership invariance of the tube itself.

Therefore the translated compact-support route cannot transport the Jost/ET
real-edge hypotheses by asserting membership invariance.  It must use one of
the following honest repairs:

1. a translated-PET extension for the selected OS witness, analogous to the
   `BHWTranslation.lean` `F_ext_on_translatedPET` package, so the translated
   positive-time branch is evaluated through a PET witness rather than through
   raw `BHW.extendF` membership; or
2. a reduced-difference-coordinate formulation in which uniform translations
   are quotient-killed before the Jost/ET hypotheses are applied.

The only honest raw-`extendF` translation theorem has **ET hypotheses**, not PET
hypotheses.  It is useful as an adapter on points that already lie in the
ordinary extended tube, but it is not a membership-transport theorem and does
not by itself justify applying a sector-local BHW branch theorem at a translated
real point:

```lean
theorem bvt_extendF_realTimeTranslate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (A : ℝ)
    (x : NPointDomain d n)
    (hxET : BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hxAET :
      BHW.realEmbed (positiveTimeTranslate (d := d) (n := n) A x) ∈
        BHW.ExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.realEmbed (positiveTimeTranslate (d := d) (n := n) A x)) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
```

These are real-translation invariance facts, not complex-time translation
facts.  They should be proved from existing BHW translation-invariance
geometry and always retain the two ET-membership hypotheses.  They do not
assume local commutativity of `bvt_W OS lgc`.  The value theorem
`bvt_extendF_realTimeTranslate` should use the absolute forward-tube input
already exposed as
`bvt_absoluteForwardTubeInput`: descend to the reduced/Route-1 BHW extension,
use the algebraic translation-invariance of the reduced pullback, and identify
it back with `BHW.extendF (bvt_F OS lgc n)` on `ExtendedTube`.  This is the same
translation-invariance mechanism as `BHWTranslation.lean`, but with the
selected OS witness instead of an already-packaged `WightmanFunctions` object.

#### 6.7.1. Selected-OS translated-PET repair package

The repair above should be implemented as a selected-OS analogue of the already
proved `BHWTranslation.lean` translated-PET package.  This is the next proof-doc
unit that must be made Lean-ready before any branch-envelope theorem consumes
translated positive-time support.

The following theorem shape is now explicitly rejected:

```lean
-- wrong surface: raw `BHW.extendF` is only the ordinary ET branch,
-- not the full PET extension.
theorem bvt_extendF_translation_invariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n) (fun k μ => z k μ + c μ) =
      BHW.extendF (bvt_F OS lgc n) z
```

Reason: `BHW.extendF F` is the choice-based complex-Lorentz extension from the
forward tube to the ordinary `BHW.ExtendedTube`.  The full PET value in
`BHWTranslation.lean` is `(W_analytic_BHW Wfn n).val`, not raw
`BHW.extendF`.  For theorem 2 we cannot use
`W_analytic_BHW (os_to_wightman_full OS lgc) n`, because its uniqueness proof
uses `Wfn.locally_commutative`, which is exactly the target theorem.

The first corrected theorem slot is the ET-local adapter:

```lean
theorem bvt_extendF_translation_invariant_on_ET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ BHW.ExtendedTube d n) :
    BHW.extendF (bvt_F OS lgc n) (fun k μ => z k μ + c μ) =
      BHW.extendF (bvt_F OS lgc n) z
```

This adapter is still nontrivial, but its domain matches raw `extendF`.  It
should be proved by identifying raw `extendF (bvt_F OS lgc n)` on ET with the
Route-1 reduced pullback associated to `bvt_absoluteForwardTubeInput`, then
using algebraic translation-invariance of the reduced pullback.

The PET-level object must be a selected OS extension value, not raw
`BHW.extendF`.  The theorem-2 route needs the following existence package:

```lean
theorem bvt_selectedPETExtension_exists
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ Fpet : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fpet (PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, Fpet z = bvt_F OS lgc n z) ∧
      (∀ z ∈ BHW.ExtendedTube d n,
        Fpet z = BHW.extendF (bvt_F OS lgc n) z) ∧
      (∀ (z : Fin n → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n →
        Fpet (fun k μ => z k μ + c μ) = Fpet z)
```

Once this theorem exists, the selected extension is chosen in the usual way:

```lean
noncomputable def bvt_F_PETExtension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (bvt_selectedPETExtension_exists OS lgc n).choose

theorem bvt_F_PETExtension_eq_extendF_on_ET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d n) :
    bvt_F_PETExtension OS lgc n z =
      BHW.extendF (bvt_F OS lgc n) z

theorem bvt_F_PETExtension_translation_invariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    bvt_F_PETExtension OS lgc n (fun k μ => z k μ + c μ) =
      bvt_F_PETExtension OS lgc n z
```

The proof of `bvt_selectedPETExtension_exists` must follow the non-circular
Route-1/reduced-difference pattern:

1. split the `n = 0` and `n = m + 1` cases;
2. instantiate the absolute forward-tube input
   `bvt_absoluteForwardTubeInput OS lgc m`;
3. descend it with `BHW.descendAbsoluteForwardTubeInput`;
4. build or reuse the reduced BHW extension for that descended input;
5. pull it back along `reducedDiffMap`;
6. prove the pulled-back extension is algebraically translation-invariant by
   `BHW.reduced_pullback_translation_invariant`;
7. identify the pulled-back extension with raw
   `BHW.extendF (bvt_F OS lgc (m+1))` on the non-permuted ET branch;
8. use the selected OS permutation/edge-distribution package, not
   `Wfn.locally_commutative`, to glue the PET branches needed by theorem 2.

The missing substep is item 4 plus the PET gluing part of item 8 for a selected
OS input.  The current `BHWTranslation.lean` implementation proves the same
translation-invariance pattern for an already packaged `WightmanFunctions`
object using `route1AbsoluteBHWExtensionCanonical` and
`W_analytic_BHW_unique`; theorem 2 cannot instantiate that route with
`os_to_wightman_full OS lgc`, because that structure already contains locality.
So the theorem-2 repair must either generalize the Route-1 reduced extension
from `WightmanFunctions` to a non-circular selected OS input carrying
`bvt_F_acrOne_package`, or prove the same comparison directly for
`bvt_absoluteForwardTubeInput`.

Implementation status after the generic `TranslatedPET` value API: the TPET
witness-independence algebra is no longer a blocker.  The generic API now also
includes the permutation-inheritance lemmas

```lean
theorem translatedPETValue_perm_invariant
theorem translatedPETValueTotal_perm_invariant
```

These say that if a PET scalar is invariant under uniform translations on PET
and under coordinate permutations on PET, then its translated-PET value and
total translated-PET value have the same permutation invariance.  This removes
the need to copy the `BHWTranslation.lean` witness-choice proof for the
selected OS scalar.

This is only algebra.  It does **not** construct the selected OS PET scalar and
it does not prove permutation invariance of that scalar.  The remaining
implementation blocker is specifically the PET scalar `bvt_F_PETExtension`,
its PET translation invariance, and its PET permutation invariance:

```lean
-- the exact hard input now needed by `translatedPETValue`
theorem bvt_F_PETExtension_translation_invariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d n) :
    bvt_F_PETExtension OS lgc n (fun k μ => z k μ + c μ) =
      bvt_F_PETExtension OS lgc n z

theorem bvt_F_PETExtension_perm_invariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d n)
    (hσz : (fun k => z (σ k)) ∈ PermutedExtendedTube d n) :
    bvt_F_PETExtension OS lgc n (fun k => z (σ k)) =
      bvt_F_PETExtension OS lgc n z
```

The tempting shortcut is invalid:

```lean
-- forbidden/circular: constructs a full WightmanFunctions record in order to
-- call `W_analytic_BHW` or `W_analytic_BHW_unique`
let Wfn := os_to_wightman_full OS lgc
```

Reason: `os_to_wightman_full` contains the theorem-2 locality field being
proved.  Likewise, the existing `BHWTranslation.lean::bhw_translation_invariant`
is not a selected-OS theorem; its proof uses `W_analytic_BHW_unique`, whose BHW
theorem input includes `Wfn.locally_commutative`.

Therefore the next production theorem must have one of the following non-
circular shapes.

First possible route: generalize Route 1 away from `WightmanFunctions`.

```lean
-- Generic selected reduced/PET route.  The statement should not mention
-- `WightmanFunctions`, and should consume an `AbsoluteForwardTubeInput` plus
-- the reduced boundary/permutation edge data that replaces global locality.
theorem selectedPETExtension_exists_of_absoluteInput
    {Wabs : SchwartzNPoint d (m + 1) → ℂ}
    (hAbs : BHW.AbsoluteForwardTubeInput (d := d) m Wabs)
    (hEdge :
      -- compact-test permutation/edge equality for the selected input,
      -- strong enough to replace `IsLocallyCommutativeWeak`
      BHW.SelectedPermutationEdgeData d m hAbs.toFun Wabs) :
    ∃ Fpet : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fpet (PermutedExtendedTube d (m + 1)) ∧
      (∀ z ∈ ForwardTube d (m + 1), Fpet z = hAbs.toFun z) ∧
      (∀ (z : Fin (m + 1) → Fin (d + 1) → ℂ)
          (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d (m + 1) →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1) →
        Fpet (fun k μ => z k μ + c μ) = Fpet z)
```

This route should reuse the already checked algebra
`BHW.reduced_pullback_translation_invariant`; its hard analytic input is the
selected reduced BHW/PET existence and gluing theorem, not the TPET translation
choice argument.

Second possible route: prove only the selected translation-invariant PET scalar
needed by theorem 2, postponing full PET permutation invariance.

```lean
theorem bvt_selectedPETTranslationScalar_exists
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    ∃ Fpet : (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fpet (PermutedExtendedTube d (m + 1)) ∧
      (∀ z ∈ ForwardTube d (m + 1), Fpet z = bvt_F OS lgc (m + 1) z) ∧
      (∀ z ∈ BHW.ExtendedTube d (m + 1),
        Fpet z = BHW.extendF (bvt_F OS lgc (m + 1)) z) ∧
      (∀ (z : Fin (m + 1) → Fin (d + 1) → ℂ)
          (c : Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d (m + 1) →
        (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1) →
        Fpet (fun k μ => z k μ + c μ) = Fpet z)
```

This narrower route is enough for `translatedPETValue`, the compact
positive-time support argument, and the newly available
`translatedPETValueTotal_perm_invariant` theorem.  It still must not be proved
from global `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.  Its proof should
identify `Fpet` with the reduced pullback on PET and with raw `BHW.extendF`
only on the ordinary ET branch, where raw `extendF` is meaningful.

The next proof-doc gap is therefore narrower than before:

1. formulate the selected reduced/PET extension construction that yields a
   `ReducedBHWExtensionData` for
   `bvt_selectedReducedForwardTubeInput OS lgc χ m`;
2. prove that the pulled-back scalar
   `bvt_selectedPETExtensionOfReducedData OS lgc m Fred` is the desired
   `bvt_F_PETExtension` on PET;
3. export its PET translation invariance from
   `bvt_selectedPETExtensionOfReducedData_translate_on_PET`;
4. export its PET permutation invariance from the `Fred.perm_invariant` field
   and `permOnReducedDiff_reducedDiffMap`;
5. only then instantiate the generic translated-PET permutation theorem.

No production theorem should define `bvt_F_PETExtension` by a dummy total
function, by raw `BHW.extendF` off ordinary ET, or by choosing
`os_to_wightman_full OS lgc`.

For both routes, the first Lean-ready preinput sublemmas are now implemented:

```lean
theorem bvt_route1AbsolutePrePullback_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    bvt_route1AbsolutePrePullback OS lgc m (fun k μ => z k μ + c μ) =
      bvt_route1AbsolutePrePullback OS lgc m z

theorem bvt_route1AbsolutePrePullback_eq_bvt_F_on_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1)) :
    bvt_route1AbsolutePrePullback OS lgc m z =
      bvt_F OS lgc (m + 1) z

theorem bvt_selectedPETExtensionOfReducedData_holomorphicOn_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData ... ) :
    DifferentiableOn ℂ
      (bvt_selectedPETExtensionOfReducedData OS lgc m Fred)
      (BHW.PermutedExtendedTube d (m + 1))

theorem bvt_selectedPETExtensionOfReducedData_permInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData ... )
    (σ : Equiv.Perm (Fin (m + 1)))
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d (m + 1))
    (hσz : (fun k => z (σ k)) ∈
      BHW.PermutedExtendedTube d (m + 1)) :
    bvt_selectedPETExtensionOfReducedData OS lgc m Fred
        (fun k => z (σ k)) =
      bvt_selectedPETExtensionOfReducedData OS lgc m Fred z
```

Thus, once the real selected extension datum `Fred` is constructed, the
following parts are already Lean-ready and compiled:

1. PET holomorphy of the absolute pullback;
2. PET translation invariance of the absolute pullback;
3. PET permutation invariance of the absolute pullback;
4. agreement with the selected OS witness on the forward tube;
5. generic promotion of PET translation/permutation invariance to
   translated-PET values.

The only remaining unfilled selected-PET scalar gap is the construction of the
datum `Fred` itself, with the correct non-circular BHW/PET extension theorem.
That construction must be the next proof-doc target.

These sublemmas are algebraic/reduced-coordinate and forward-tube comparison
statements.  They isolate the selected translation-invariant preinput without
mentioning PET gluing or locality.  They must not be mistaken for the selected
PET extension: outside the forward tube, `bvt_route1AbsolutePrePullback`
evaluates the original total forward-tube witness on a safe representative, and
is not known to be holomorphic on ET/PET or to agree with raw `BHW.extendF`.

The next hard theorem surface is therefore **not** the following overstrong
statement about the pre-pullback:

```lean
-- do not try to prove this for the pre-pullback alone
theorem bvt_route1AbsolutePrePullback_eq_extendF_on_ET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ExtendedTube d (m + 1)) :
    bvt_route1AbsolutePrePullback OS lgc m z =
      BHW.extendF (bvt_F OS lgc (m + 1)) z
```

That statement would require precisely the missing selected reduced BHW/PET
extension.  The correct next production theorem should first construct a
selected reduced BHW extension `Fred` from the selected OS input and selected
edge/permutation data, then define the PET scalar as its absolute pullback:

```lean
noncomputable def bvt_selectedPETExtension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ :=
  BHW.pullbackReducedExtension
    (bvt_selectedReducedBHWExtension OS lgc m)

theorem bvt_selectedPETExtension_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ) :
    bvt_selectedPETExtension OS lgc m (fun k μ => z k μ + c μ) =
      bvt_selectedPETExtension OS lgc m z
```

The translation theorem is then immediate from
`BHW.reduced_pullback_translation_invariant`.  The hard part is the existence
and uniqueness/gluing theorem for `bvt_selectedReducedBHWExtension`, including
agreement with the pre-pullback on `ReducedForwardTubeN` and agreement with raw
`BHW.extendF (bvt_F OS lgc (m+1))` on the ordinary ET branch.  This is exactly
where selected OS edge-distribution data replaces the forbidden global
`Wfn.locally_commutative`.

The implementation-ready part of this paragraph is now in production in its
honest "given reduced data" form:

```lean
noncomputable def bvt_selectedPETExtensionOfReducedData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ

theorem bvt_selectedPETExtensionOfReducedData_translate_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (hz : z ∈ PermutedExtendedTube d (m + 1))
    (hzc : (fun k μ => z k μ + c μ) ∈ PermutedExtendedTube d (m + 1)) :
    bvt_selectedPETExtensionOfReducedData OS lgc m Fred
        (fun k μ => z k μ + c μ) =
      bvt_selectedPETExtensionOfReducedData OS lgc m Fred z

theorem bvt_selectedPETExtensionOfReducedData_eq_bvt_F_on_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ)
    (hz : z ∈ ForwardTube d (m + 1)) :
    bvt_selectedPETExtensionOfReducedData OS lgc m Fred z =
      bvt_F OS lgc (m + 1) z
```

This closes the reduced-pullback algebra seam.  It deliberately does not
construct `Fred`.  The next proof-doc item must therefore specify the exact
non-circular construction of

```lean
Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
  (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
    (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun
```

from selected OS edge-distribution/permutation data.

The reduced forward-tube input required by that theorem is no longer a gap.
Production now constructs it directly from the selected OS witness:

```lean
noncomputable def bvt_reducedWightmanFamily
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d) :
    (m : ℕ) → SchwartzNPoint d m → ℂ

theorem bvt_selectedReducedBoundaryValues
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    BHW.HasReducedBoundaryValues (d := d)
      (bvt_reducedWightmanFamily OS lgc χ) m
      (BHW.descendAbsoluteForwardTubeInput (d := d) (m := m)
        (bvt_absoluteForwardTubeInput (d := d) OS lgc m)).toFun

noncomputable def bvt_selectedReducedForwardTubeInput
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    BHW.ReducedForwardTubeInput (d := d)
      (bvt_reducedWightmanFamily OS lgc χ) m
```

The proof is the exact reduced/absolute change-of-variables argument already
used for the Route-1 spectrum-condition input, but specialized non-circularly
to `bvt_F`/`bvt_W`: `bvt_selectedReducedPreInput_factorization_absoluteApproach`
identifies the descended preinput with the absolute `bvt_F` approach point,
`bvt_selectedReducedBoundaryIntegral_eq_absoluteBoundaryIntegral` integrates
out the normalized basepoint cutoff, and `bvt_boundary_values` supplies the
limit.  No PET gluing, `W_analytic_BHW_unique`, `os_to_wightman_full`, or
locality input is used.

Consequently the next hard theorem surface is now narrower, but one correction
is essential.  The OS/BHW route must construct edge data only for adjacent
transpositions, not for arbitrary finite permutations.  Arbitrary permutations
can have empty real edge overlap in high arity, so an all-permutation
`V.Nonempty` witness is too strong to be the construction target.

The active selected edge-data structure and adjacent overlap adapter are now
implemented in `OSToWightmanSelectedWitness.lean`:

```lean
structure SelectedAdjacentPermutationEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) : Prop where
  overlap_connected :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
              BHW.ExtendedTube d n}
  edge_witness :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∃ V : Set (NPointDomain d n),
        IsOpen V ∧ V.Nonempty ∧
        (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) ∧
        (∀ x ∈ V,
          BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
            BHW.ExtendedTube d n) ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) * φ x
            =
          ∫ x : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x)

theorem bvt_F_extendF_adjacent_overlap_of_selectedEdgeData
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∀ z, z ∈ BHW.ExtendedTube d n →
      BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
        BHW.ExtendedTube d n →
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩) z) =
        BHW.extendF (bvt_F OS lgc n) z

def BHW.permutedExtendedTubeSector (d n : ℕ) (π : Equiv.Perm (Fin n))
theorem BHW.isOpen_permutedExtendedTubeSector
theorem BHW.permutedExtendedTube_eq_iUnion_sectors
theorem BHW.permutedExtendedTubeSector_subset_permutedExtendedTube
theorem BHW.permutedExtendedTubeSector_isPreconnected
theorem BHW.permutedExtendedTubeSector_adjacent_overlap_nonempty

def bvt_selectedPETBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  fun z => BHW.extendF (bvt_F OS lgc n) (fun k => z (π k))

theorem bvt_selectedPETBranch_holomorphicOn_sector
    (π : Equiv.Perm (Fin n)) :
    DifferentiableOn ℂ
      (bvt_selectedPETBranch OS lgc n π)
      (BHW.permutedExtendedTubeSector d n π)

theorem bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzπswap :
      z ∈ BHW.permutedExtendedTubeSector d n
        (π * Equiv.swap i ⟨i.val + 1, hi⟩)) :
    bvt_selectedPETBranch OS lgc n
        (π * Equiv.swap i ⟨i.val + 1, hi⟩) z =
      bvt_selectedPETBranch OS lgc n π z

noncomputable def bvt_selectedReducedBHWExtensionData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc (m + 1)) :
    BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_selectedReducedForwardTubeInput OS lgc χ m).toFun
```

This must be a real constructor for the `ReducedBHWExtensionData` record, not an
existential theorem with a dummy postcondition.  The record fields themselves
are the mathematical content: holomorphy on the reduced PET, agreement with the
selected reduced forward-tube input, reduced Lorentz invariance, and reduced
permutation invariance.  If the proof is not available, the implementation
should leave this as the named hard theorem/definition surface, not replace its
content by an existential with a dummy postcondition.

`SelectedAdjacentPermutationEdgeData` is not a global locality hypothesis.  Its
`edge_witness` field is exactly the compact-test equality consumed by
`BHW.extendF_perm_overlap_of_edgePairingEquality`, but only on adjacent
spacelike edges where the OS/Jost input is expected to exist.  Its
`overlap_connected` field supplies the adjacent connected-domain propagation.
The branch-cover package above is the Lean-ready local compatibility layer:
each branch is holomorphic on its own explicit sector, and adjacent branches
agree on adjacent sector overlaps.

Route correction after #1065: this paragraph is conditional on already having
`hEdge : SelectedAdjacentPermutationEdgeData OS lgc n`.  The project does not
yet have the OS proof of `hEdge`, and that proof is the current active
theorem-2 target.  Do not spend the next implementation round on PET
single-valuedness while `SelectedAdjacentPermutationEdgeData` is still only an
assumption packet.  The BHW/PET gluing work becomes live after
`bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le` is documented
and implemented in the `2 ≤ d` real-edge range.  If the public theorem remains
all-dimensional, the `d = 1` branch must be documented separately: either a
real-open edge theorem that genuinely constructs the same fields, or a direct
complex-edge boundary-locality proof that does not pretend to fill
`SelectedAdjacentPermutationEdgeData`.

The purely formal finite-cover gluing step has now been split off and
implemented in `PermutedTubeGluing.lean`.  It deliberately assumes compatibility
on all sector overlaps:

```lean
def BHW.gluedPETValue
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)

theorem BHW.gluedPETValue_eq_of_mem_sector
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hcompat :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n ρ →
        G π z = G ρ z)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π) :
    BHW.gluedPETValue G z = G π z

theorem BHW.gluedPETValue_holomorphicOn
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hG_holo :
      ∀ π, DifferentiableOn ℂ (G π) (BHW.permutedExtendedTubeSector d n π))
    (hcompat :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n ρ →
        G π z = G ρ z) :
    DifferentiableOn ℂ (BHW.gluedPETValue G) (BHW.PermutedExtendedTube d n)
```

Conditional on the OS edge packet, the next BHW-side hard gap is all-overlap
branch compatibility from adjacent overlap compatibility.

```lean
theorem bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    bvt_selectedPETBranch OS lgc n π z =
      bvt_selectedPETBranch OS lgc n ρ z
```

This is the exact point where the proof must use the BHW sector-graph/monodromy
argument: adjacent swaps generate the permutation graph and PET is the connected
analytic continuation domain for the adjacent-glued sectors.  It is not enough
to chain adjacent equalities at a fixed point, because a fixed `z` in two
non-adjacent sectors need not lie in every intermediate sector.  The proof must
obtain independence of analytic continuation over the finite open cover,
rather than asking for a nonexistent all-permutation real edge.

The Lean implementation is therefore not ready to close this BHW-side theorem
from the current local data alone.  The missing item is a BHW
cover-gluing/monodromy
theorem, not another wrapper around `SelectedAdjacentPermutationEdgeData`.

Historical diagnostic, now quarantined after the #1049/#1061 audits: one
tempting route was a **fixed-fiber sector graph theorem**:

```lean
def BHW.petSectorAdjStep
    (z : Fin n → Fin (d + 1) → ℂ)
    (π ρ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (i : Fin n) (hi : i.val + 1 < n),
    ρ = π * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
      z ∈ BHW.permutedExtendedTubeSector d n π ∧
      z ∈ BHW.permutedExtendedTubeSector d n ρ

theorem BHW.petSectorFiber_adjacent_connected
    [NeZero d]
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    Relation.ReflTransGen
      (BHW.petSectorAdjStep (d := d) (n := n) z) π ρ
```

If this theorem were true, then the PET branch-independence proof would be
elementary:
induct over the `Relation.ReflTransGen` chain.  Each adjacent edge in the chain
keeps the same point `z` inside both neighboring sectors, so the local adjacent
equality hypothesis applies directly at `z`.  This gives an implementation-ready
conditional theorem:

```lean
theorem BHW.extendF_pet_branch_independence_of_adjacent_of_sectorFiberConnected
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAdj :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) →
        BHW.extendF F (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
          BHW.extendF F (fun k => z (π k)))
    (hFiber :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n ρ →
        Relation.ReflTransGen
          (BHW.petSectorAdjStep (d := d) (n := n) z) π ρ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π →
      z ∈ BHW.permutedExtendedTubeSector d n ρ →
      BHW.extendF F (fun k => z (π k)) =
        BHW.extendF F (fun k => z (ρ k))
```

Lean proof skeleton:

```lean
  intro π ρ z hzπ hzρ
  have hchain := hFiber π ρ z hzπ hzρ
  induction hchain with
  | refl => rfl
  | tail hprev hlast ih =>
      rcases hlast with ⟨i, hi, rfl, hleft, hright⟩
      exact ih.trans (hAdj _ i hi z hleft hright).symm
```

The proof direction may need `ih.symm.trans ...` depending on the chosen
orientation of `petSectorAdjStep`, but no analytic theorem is hidden in this
adapter.  All genuine geometry is isolated in
`BHW.petSectorFiber_adjacent_connected`.

The incorrect pointwise route is already visible in the older
`BHWPermutation/PermutationFlow.lean` scaffolding:

```lean
Relation.ReflTransGen (etAdjStep (d := d) (n := n) y) 1 τ
```

or its midpoint form

```lean
permAct (d := d) (σ * Equiv.swap i ⟨i.val + 1, hi⟩) y ∈
    BHW.ExtendedTube d n →
  permAct (d := d) σ y ∈ BHW.ExtendedTube d n
```

This is too strong for the PET all-overlap theorem.  It asks for a single
configuration `y` to remain inside ET along a chosen adjacent-swap word.  The
whole reason to use PET is that analytic continuation can move through the
sector cover even when that fixed configuration is not in the intermediate
absolute ET sectors.

The corrected fixed-fiber theorem above is not the same as the old midpoint
condition.  It does not demand that every adjacent decomposition of
`ρ * π⁻¹` works, nor that one can always drop the final adjacent swap.  It asks
only for the existence of some adjacent path inside the sector labels that
actually contain the given `z`.  This is the exact geometry claim to verify
next.  If it fails, the route must switch to a genuine germ-level monodromy
theorem whose continuation path is allowed to move the base point in PET.

Existing private connected-index scaffolding in
`BHWPermutation/PermutationFlow.lean` should not be mistaken for this theorem.
The older lemmas around

```lean
permForwardOverlapSet
permForwardOverlapIndexSet
isConnected_permForwardOverlapSet_of_indexConnected
extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected
```

address a different question: for a fixed permutation `σ`, is the two-sector
overlap `{z | z ∈ ET ∧ σ·z ∈ ET}` connected enough to propagate equality from a
real Jost edge?  That route needs either a Jost witness in the overlap or
strong index-connectedness hypotheses.  It remains useful for conditional
overlap uniqueness, but it does not by itself prove that the set of sector
labels containing a given PET point is adjacent-connected.

The historical diagnostic was binary:

1. Prove `BHW.petSectorFiber_adjacent_connected`.  Then implement
   `BHW.extendF_pet_branch_independence_of_adjacent_of_sectorFiberConnected`
   by the chain induction above, instantiate `hFiber`, and close
   `BHW.extendF_pet_branch_independence_of_adjacent`.
2. If `BHW.petSectorFiber_adjacent_connected` is false, stop trying fixed-point
   chains.  Replace it with a true monodromy theorem over the adjacent-glued
   Riemann domain of germs.  That theorem must explicitly prove that the two
   germs over a common PET point have the same analytic continuation value,
   not merely that PET is preconnected as a subset of affine space.

The #1049/#1061 correction selects the second branch for the active route.
`BHW.petSectorFiber_adjacent_connected` and its reachable-label/orbit-chamber
adapters may remain as conditional lemmas, but they are **not** construction
targets unless the fixed-fiber geometry is independently rehabilitated by a
real proof.  The active target is the germ-level monodromy theorem below.

#### Forward-tube model for the fixed-fiber theorem

The ordinary permuted forward-tube cover has no nontrivial fixed-fiber graph.
This is now checked:

```lean
theorem BHW.permutedForwardTube_sector_eq_of_mem
    (π ρ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hzπ : z ∈ BHW.PermutedForwardTube d n π)
    (hzρ : z ∈ BHW.PermutedForwardTube d n ρ) :
    π = ρ
```

Proof idea: if `w := z ∘ π` lies in `ForwardTube d n`, and
`z ∘ ρ` also lies in `ForwardTube d n`, then `w` lies in
`PermutedForwardTube d n (π⁻¹ * ρ)`.  The existing theorem
`permutedForwardTube_forces_perm_one` forces `π⁻¹ * ρ = 1`, hence `π = ρ`.

Consequences for the PET proof:

1. `BHW.petSectorFiber_adjacent_connected` is not a combinatorial fact about
   forward-tube orderings; forward-tube fibers are singletons.
2. Any nontrivial sector-label fiber over a PET point comes from the
   `ExtendedTube` existential witnesses, i.e. from different complex Lorentz
   frames representing different reordered configurations.
3. A proof of `BHW.petSectorFiber_adjacent_connected` therefore needs an
   additional **common-frame / orbit-fiber** theorem.  The shape is schematic,
   not yet a Lean target:

```lean
Input:
  z ∈ S π and z ∈ S ρ.
Output:
  either a single Lorentz frame reducing both memberships to the ordinary
  permuted-forward-tube singleton theorem, or an adjacent sector-label path
  over the fixed point `z` built from orbit witnesses.
```

The exact common-frame theorem is not yet mathematically specified.  The next
proof-doc work must identify the correct orbit-fiber statement.  It is not
enough to cite
`permutedExtendedTube_isPreconnected`, because connectedness of PET as a set
does not control the discrete label fiber over one point.

The general two-label fixed-fiber theorem has also been reduced to the
identity-label case:

```lean
theorem BHW.petSectorFiber_adjacent_connected_of_identity_chain
    (hChain :
      ∀ (σ : Equiv.Perm (Fin n))
        (y : Fin n → Fin (d + 1) → ℂ),
        y ∈ BHW.ExtendedTube d n →
        (fun k => y (σ k)) ∈ BHW.ExtendedTube d n →
        Relation.ReflTransGen
          (BHW.petSectorAdjStep (d := d) (n := n) y)
          (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π →
      z ∈ BHW.permutedExtendedTubeSector d n ρ →
      Relation.ReflTransGen
        (BHW.petSectorAdjStep (d := d) (n := n) z) π ρ
```

The proof sets `σ := π⁻¹ * ρ` and `y := z ∘ π`.  Then `z ∈ S π` becomes
`y ∈ ET`, while `z ∈ S ρ` becomes `y ∘ σ ∈ ET`; the identity-chain hypothesis
gives a chain from `1` to `σ`, and left multiplication by `π` transports it
back to a chain from `π` to `ρ` over the original fixed point `z`.

So the remaining fixed-fiber geometry target is now:

```lean
theorem BHW.petSectorFiber_identity_chain
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (y : Fin n → Fin (d + 1) → ℂ)
    (hy : y ∈ BHW.ExtendedTube d n)
    (hσy : (fun k => y (σ k)) ∈ BHW.ExtendedTube d n) :
    Relation.ReflTransGen
      (BHW.petSectorAdjStep (d := d) (n := n) y)
      (1 : Equiv.Perm (Fin n)) σ
```

This is exactly the old `hChain` hypothesis from the private
`PermutationFlow.lean` wrapper, but now isolated without the overstrong
`hmidCond`.  The implementation-ready consumer exists; the mathematical gap is
the identity-chain geometry theorem itself.

The identity-chain theorem has been reduced once more to the forward-tube-start
case.  The checked Lorentz-invariance lemma is:

```lean
theorem BHW.permutedExtendedTubeSector_complexLorentzAction_iff
    (Λ : ComplexLorentzGroup d)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    BHW.complexLorentzAction Λ z ∈ BHW.permutedExtendedTubeSector d n π ↔
      z ∈ BHW.permutedExtendedTubeSector d n π
```

Using it, the checked reduction is:

```lean
theorem BHW.petSectorFiber_identity_chain_of_forwardTube_chain
    (hChainFT :
      ∀ (σ : Equiv.Perm (Fin n))
        (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        (fun k => w (σ k)) ∈ BHW.ExtendedTube d n →
        Relation.ReflTransGen
          (BHW.petSectorAdjStep (d := d) (n := n) w)
          (1 : Equiv.Perm (Fin n)) σ) :
    ∀ (σ : Equiv.Perm (Fin n))
      (y : Fin n → Fin (d + 1) → ℂ),
      y ∈ BHW.ExtendedTube d n →
      (fun k => y (σ k)) ∈ BHW.ExtendedTube d n →
      Relation.ReflTransGen
        (BHW.petSectorAdjStep (d := d) (n := n) y)
        (1 : Equiv.Perm (Fin n)) σ
```

Proof idea: choose an extended-tube witness `y = Λ • w` with `w ∈ FT`.
Since Lorentz action commutes with coordinate permutations, `y ∘ σ ∈ ET`
implies `w ∘ σ ∈ ET` after applying `Λ⁻¹`.  The forward-tube-chain hypothesis
gives the chain over `w`, and sector-membership Lorentz invariance transports
each adjacent step back to `y`.

So the remaining fixed-fiber geometry target is now even sharper:

```lean
theorem BHW.petSectorFiber_forwardTube_chain
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ BHW.ForwardTube d n)
    (hσw : (fun k => w (σ k)) ∈ BHW.ExtendedTube d n) :
    Relation.ReflTransGen
      (BHW.petSectorAdjStep (d := d) (n := n) w)
      (1 : Equiv.Perm (Fin n)) σ
```

This theorem says: if a forward-tube point remains in the extended tube after a
permutation, then there is an adjacent-swap path from the identity ordering to
that permutation, and every intermediate reordered point remains in the
extended tube.  This is a purely BHW orbit/fiber geometry statement.  It is
strictly weaker and cleaner than the old `hmidCond`, but it is still not proved
by the existing PET connectedness theorem.

A natural but ultimately overstrong geometry lemma is the forward-tube-start
suffix-removal property:

```lean
theorem BHW.forwardTube_chain_suffixRemoval
    [NeZero d]
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ BHW.ForwardTube d n)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (hσswap :
      (fun k => w ((σ * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈
        BHW.ExtendedTube d n) :
    (fun k => w (σ k)) ∈ BHW.ExtendedTube d n
```

If true, `BHW.petSectorFiber_forwardTube_chain` would follow by
`Fin.Perm.adjSwap_induction_right`: decompose `σ` as
`σ₀ * swap(i,i+1)`, use suffix-removal to obtain the intermediate endpoint
`w ∘ σ₀ ∈ ET`, apply the induction hypothesis to get a chain from `1` to
`σ₀`, then append the adjacent step from `σ₀` to `σ₀ * swap(i,i+1)`.
This conditional adapter is now checked:

```lean
theorem BHW.petSectorFiber_forwardTube_chain_of_suffixRemoval
    (hSuffix :
      ∀ (w : Fin n → Fin (d + 1) → ℂ),
        w ∈ BHW.ForwardTube d n →
        ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n),
          (fun k => w ((σ * Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈
            BHW.ExtendedTube d n →
          (fun k => w (σ k)) ∈ BHW.ExtendedTube d n) :
    ∀ (σ : Equiv.Perm (Fin n))
      (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ BHW.ForwardTube d n →
      (fun k => w (σ k)) ∈ BHW.ExtendedTube d n →
      Relation.ReflTransGen
        (BHW.petSectorAdjStep (d := d) (n := n) w)
        (1 : Equiv.Perm (Fin n)) σ
```

This suffix-removal statement is close to the old private `hmidCond`, but even
with the two intended corrections it is still too strong:

1. it is restricted to a starting point `w ∈ ForwardTube d n`, after using the
   checked Lorentz reduction above;
2. it is a sufficient theorem, not the definition of the route.  If it is false,
   the weaker existential chain theorem may still hold.

It is false in this unrestricted form.  Take `n = 2`, `d ≥ 1`, and the
collinear imaginary-time forward-tube point

```text
w₀ = i e₀,
w₁ = 2 i e₀.
```

Then `w ∈ FT`: the first imaginary vector is `e₀ ∈ V_+`, and the successive
difference has imaginary part `e₀ ∈ V_+`.  Apply suffix-removal with
`σ = swap(0,1)` and the same adjacent swap.  Since `σ * swap = 1`, the
hypothesis is just `w ∈ ET`, which follows from `w ∈ FT`.  The conclusion
would be `w ∘ swap ∈ ET`.

But `w ∘ swap = (2 i e₀, i e₀)` cannot lie in `ET`.  Indeed, if some complex
Lorentz transform `Λ` sent it into `FT`, then writing `u := Λ(i e₀)`, the two
transformed coordinates would be `2u` and `u`.  The forward-tube conditions
would force both

```text
Im(2u) ∈ V_+
Im(u - 2u) = - Im(u) ∈ V_+,
```

which is impossible because the open future cone contains no vector together
with its negative.  The Lorentz action preserves the linear relation between
the two coordinates, so no alternate frame escapes this contradiction.
The checked helper

```lean
theorem BHW.mem_extendedTube_iff_exists_lorentz_mem_forwardTube
```

is exactly the Lean doorway for formalizing this argument: it replaces
`w ∘ swap ∈ ET` by the existence of a forwardizing complex Lorentz frame.

Thus suffix-removal is a useful diagnostic only: it explains one sufficient
monotone route, but it is not an active target and must not be introduced as an
axiom or production assumption.

The exact failed set-theoretic form is:

```lean
BHW.permForwardOverlapSet (d := d) n
    (σ * Equiv.swap i ⟨i.val + 1, hi⟩)
  ⊆
BHW.permForwardOverlapSet (d := d) n σ
```

because

```lean
BHW.permForwardOverlapSet (d := d) n τ
  = {w | w ∈ BHW.ForwardTube d n ∧
          (fun k => w (τ k)) ∈ BHW.ExtendedTube d n}
```

So suffix-removal would say the forward-overlap sets are downward closed under
right weak-order deletion of a final adjacent generator.  The `n = 2` example
above shows that this downward-closedness fails: for `σ = swap`, deleting the
final adjacent generator lands at the identity set, and the implication would
force the whole forward tube into the adjacent-swap forward-overlap set.

The corrected proof-doc task is therefore:

1. Do **not** try to prove weak-order downward-closedness of
   `permForwardOverlapSet`.
2. Determine whether the weaker existential theorem
   `BHW.petSectorFiber_forwardTube_chain` is true by a non-monotone adjacent
   path inside the reachable-label set
   `{σ | (fun k => w (σ k)) ∈ ET}`.
3. If the fixed-fiber reachable-label theorem is false or too hard, switch to
   a genuine germ-level monodromy theorem over the adjacent-glued PET sector
   cover.

The fixed-fiber route should now be formulated as graph connectivity, not
monotonicity:

```lean
def BHW.petReachableLabelSet
    (w : Fin n → Fin (d + 1) → ℂ) :
    Set (Equiv.Perm (Fin n)) :=
  {σ | (fun k => w (σ k)) ∈ BHW.ExtendedTube d n}

theorem BHW.petReachableLabelSet_adjacent_connected
    [NeZero d]
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ BHW.ForwardTube d n)
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∈ BHW.petReachableLabelSet (d := d) (n := n) w) :
    Relation.ReflTransGen
      (fun α β =>
        ∃ (i : Fin n) (hi : i.val + 1 < n),
          β = α * Equiv.swap i ⟨i.val + 1, hi⟩ ∧
          α ∈ BHW.petReachableLabelSet (d := d) (n := n) w ∧
          β ∈ BHW.petReachableLabelSet (d := d) (n := n) w)
      (1 : Equiv.Perm (Fin n)) σ
```

This theorem is exactly equivalent to `BHW.petSectorFiber_forwardTube_chain`
after unfolding `petSectorAdjStep` at a forward-tube base point.  Unlike
suffix-removal, it does not specify a particular reduced word and does not
claim the reachable set is a weak-order ideal.

The Lean surface now reflects this corrected target:

```lean
def BHW.petReachableLabelSet
def BHW.petReachableLabelAdjStep

theorem BHW.one_mem_petReachableLabelSet_of_forwardTube
theorem BHW.mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube
theorem BHW.petReachableLabelSet_adjacent_connected_of_orbitChamberConnected
theorem BHW.petSectorFiber_forwardTube_chain_of_reachableLabelConnected
theorem BHW.petSectorFiber_adjacent_connected_of_reachableLabelConnected
theorem BHW.extendF_pet_branch_independence_of_adjacent_of_reachableLabelConnected
theorem BHW.extendF_pet_branch_independence_of_adjacent_of_orbitChamberConnected
```

The orbit/chamber characterization says:

```lean
σ ∈ petReachableLabelSet w
  ↔ ∃ Λ : ComplexLorentzGroup d,
      complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ
```

So the reachable labels are exactly the ordinary forward-tube chambers hit by
the complex Lorentz orbit of `w`.  The checked adapters now carry
reachable-label graph connectivity all the way to the desired all-overlap PET
branch equality:

```lean
orbitChamberConnected
  → petReachableLabelSet_adjacent_connected
  → petSectorFiber_forwardTube_chain
  → petSectorFiber_adjacent_connected
  → extendF_pet_branch_independence_of_adjacent
```

The unproved mathematical content is therefore exactly the chamber-hit
graph-connectivity theorem for this orbit, not any monotone suffix deletion
principle and not another analytic wrapper.

A plausible proof path is now an orbit/chamber crossing theorem:

```lean
theorem BHW.orbit_permutedForwardTube_chamberHitGraph_connected
    [NeZero d]
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ BHW.ForwardTube d n) :
    -- the induced adjacent-Cayley graph on
    -- {σ | ∃ Λ, complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ}
    -- is connected from `1`
    ...
```

This should be proved, if true, by applying a path in the connected complex
Lorentz group from `1` to a forwardizing frame for `σ`, and showing that the
set of ordinary chamber labels hit along the orbit path changes only through
adjacent chamber crossings.  The missing geometry is the chamber-crossing
lemma: an orbit path cannot jump from one ordinary permuted forward-tube
chamber to a non-adjacent chamber without hitting a chain of adjacent chamber
closures.  This is now the most concrete fixed-fiber proof-doc target.

Important caution: connectedness of `ComplexLorentzGroup d` alone is **not**
enough.  For a fixed `w`, the sets

```lean
{Λ | BHW.complexLorentzAction Λ w ∈ BHW.PermutedForwardTube d n σ}
```

are pairwise disjoint open subsets of the group, because ordinary permuted
forward-tube chambers are disjoint.  A path from `1` to a frame hitting
`σ` may leave the union of all these chamber-hit sets for a long interval.
Therefore the proof cannot be a finite-open-cover nerve argument on the group.
It needs a stronger chamber-discretization theorem:

```lean
theorem BHW.orbit_chamber_path_discretization
    [NeZero d]
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ BHW.ForwardTube d n)
    (σ : Equiv.Perm (Fin n))
    (Λ : ComplexLorentzGroup d)
    (hΛσ :
      BHW.complexLorentzAction Λ w ∈
        BHW.PermutedForwardTube d n σ) :
    ∃ (m : ℕ) (label : Fin (m + 1) → Equiv.Perm (Fin n)),
      label 0 = 1 ∧
      label ⟨m, Nat.lt_succ_self m⟩ = σ ∧
      (∀ j, ∃ Γ : ComplexLorentzGroup d,
        BHW.complexLorentzAction Γ w ∈
          BHW.PermutedForwardTube d n (label j)) ∧
      (∀ j : Fin m, ∃ (i : Fin n) (hi : i.val + 1 < n),
        label j.succ = label j.castSucc * Equiv.swap i ⟨i.val + 1, hi⟩)
```

This statement says that every target chamber hit by the orbit can be reached
by a finite adjacent sequence of chambers **also hit by the same orbit**.  It
is precisely what `petReachableLabelSet_adjacent_connected` needs after
rewriting reachable labels via
`mem_petReachableLabelSet_iff_exists_lorentz_mem_permutedForwardTube`.

Potential geometric proof strategy:

1. Choose a continuous path `γ : [0,1] → ComplexLorentzGroup d` from `1` to
   `Λ`.
2. Track the real imaginary-time coordinates
   `t_j(s) := Im((γ(s) • w_j)_0)`.  Whenever the orbit point lies in an
   ordinary permuted forward tube, the label is the strict order of these
   coordinates, refined by the forward-cone conditions on consecutive
   differences.
3. Perturb `γ`, if necessary, so the finitely many equal-time hypersurfaces
   `t_a = t_b` are crossed generically and one at a time.
4. Prove that each generic crossing changes the strict order by one adjacent
   transposition and that the forward-cone inequalities can be preserved or
   recovered on both sides by nearby chamber-hit points.
5. Extract the finite label list from the ordered crossing times.

Step 4 is the actual missing BHW geometry.  It is not currently supplied by the
repo, and it must be proved or replaced by the germ-monodromy fallback before
we can claim the fixed-fiber route is implementation-ready.

#### Stress test of orbit/chamber discretization

Claude's review correctly warns that the orbit/chamber claim must be tested
before any more adapters are added.  A first numerical stress test in the
`d = 1`, `n = 3` complex-boost model raises a serious concern.

Represent the `1+1` complex Lorentz group by complex boosts

```text
Λ(θ) = [[cosh θ, sinh θ],
        [sinh θ, cosh θ]]
```

and sample a forward-tube point `w` with arbitrary real parts and
future-timelike imaginary increments.  For the concrete sample

```text
w₀ = (1.0576445900575475 + 1.6209368993349254 i,
      -1.8330548784085745 - 0.6745469170449656 i)
w₁ = (0.7335797734084579 + 2.4286748804806555 i,
       0.010949855196996428 - 0.5606074163819775 i)
w₂ = (0.5417748221635246 + 3.0138108111962216 i,
       1.8149305952325392 - 0.3342417063453761 i)
```

the imaginary increments are future-timelike, so `w ∈ FT`.  A dense rectangular
sample of `θ = a + i b`, with `a ∈ [-6,6]` and `b ∈ [-π,π]`, found chamber hits
only for

```text
id       = (0,1,2)
reverse  = (2,1,0)
```

and found no hits for the adjacent intermediate labels

```text
(1,0,2), (0,2,1), (1,2,0), (2,0,1).
```

The best sampled forward-cone margin for the missing intermediate chambers
remained negative; for example, at grid sizes `51, 101, 151, 201`, the best
margin for `(2,0,1)` approached zero but stayed negative in the sample.  This
is not a formal counterexample, but it is strong enough to stop treating
`orbit_chamber_path_discretization` as a safe route target.

Interpretation:

1. The local `n = 2` sanity check is harmless: a reachable set containing only
   `id`, or both `id` and the unique swap, is automatically connected.
2. In `n = 3`, the orbit-hit label set can plausibly be disconnected as an
   induced adjacent-Cayley subgraph.
3. Therefore the fixed-fiber route is now suspect.  It may fail because the
   analytic continuation path through PET can move through non-ordinary
   chamber regions, while the orbit/chamber graph records only ordinary
   permuted-forward-tube chamber hits.

Until this numerical warning is either formalized away or turned into an
explicit counterexample theorem, no further wrappers should target
`orbit_chamber_path_discretization`.  The fixed-fiber reachable-label adapters
that have already been checked in Lean are still logically sound conditional
theorems, but they are now quarantined as diagnostic infrastructure.  They
should not be used as the active construction route for theorem 2 unless the
fixed-fiber chamber claim is first rehabilitated by a real proof.

#### Route decision after the fixed-fiber audit

The next route must be a genuine PET edge/germ monodromy route.  This agrees
with the standard BHW/Jost story in spirit: the analytic continuation must move
through the adjacent-glued sector cover, with Jost real edges supplying the
local equality seeds.  It must not require a fixed point or a fixed Lorentz
orbit to hit a connected sequence of ordinary permuted forward-tube chambers.

There is an important Lean-facing correction to the informal "Jost shortcut."
The local API does **not** currently provide a theorem named or shaped like

```lean
∀ x, x ∈ BHW.JostSet d n →
  BHW.realEmbed x ∈ BHW.ExtendedTube d n
```

nor the stronger all-sector consequence

```lean
∀ x, x ∈ BHW.JostSet d n →
  ∀ π, BHW.realEmbed x ∈ BHW.permutedExtendedTubeSector d n π
```

The checked theorem is only

```lean
theorem BHW.forwardJostSet_subset_extendedTube
```

and `ForwardJostSet` is the forward ordered real edge, not a permutation-
invariant all-sector Jost edge.  By contrast, `BHW.JostSet` is permutation
invariant, but it is only the pairwise-spacelike locality support set.  Older
`PermutationFlow` code explicitly treats the full Jost-to-extended-tube bridge
as a hypothesis `hJostET`, which is the right warning sign.

The stronger warning is that the current repo `BHW.JostSet → ExtendedTube`
statement is false, not merely unproved.  In `d = 1`, `n = 2`, set

```text
x₀ = (0,  1),   x₁ = (0, -1).
```

Then each `xᵢ` is spacelike and `x₀ - x₁ = (0,2)` is spacelike, so
`x ∈ BHW.JostSet 1 2`.  But `realEmbed x ∉ BHW.ExtendedTube 1 2`.  Indeed, if
`realEmbed x ∈ ET`, then
`mem_extendedTube_iff_exists_lorentz_mem_forwardTube` gives a complex Lorentz
frame in which the transformed configuration `w` lies in `ForwardTube`.  The
linear relation `x₁ = -x₀` is preserved by every Lorentz action, so
`w₁ = -w₀`.  Forward-tube membership would require both

```text
Im(w₀) ∈ V₊,
Im(w₁ - w₀) = -2 Im(w₀) ∈ V₊,
```

which is impossible for the open future cone.  Thus the current `BHW.JostSet`
is correct for locality support, but too broad for global tube-edge membership.

Therefore the active proof docs must not write "Jost points lie in every PET
sector" as an available fact for the current `BHW.JostSet`.  Every
Lean-facing Jost-edge theorem must carry explicit local edge hypotheses:

```lean
(hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
(hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
(hV_permET :
  ∀ x ∈ V,
    BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
```

This is the current safe route.  It matches the already documented
compact-support edge-distribution package and avoids smuggling a geometric
theorem that is false for the current definition.  A future classical BHW
all-sector route would require introducing a **different, stronger**
tube-Jost set, for example a condition on all nontrivial positive convex
combinations of consecutive differences.  That would be new geometry and is
not needed for the current adjacent-edge route.

PET connectedness alone is also not enough to identify all sector branches.
To turn adjacent branch equality into all-overlap compatibility, the proof
must supply one of these real mathematical inputs:

1. a pairwise sector-overlap theorem: each relevant
   `S π ∩ S ρ` is connected/preconnected and contains a real Jost open seed
   on which the two branches agree; or
2. a genuine monodromy theorem for the adjacent-glued Riemann domain of sector
   germs over PET.

The first option is close to the older two-sector overlap machinery in
`BHWPermutation/PermutationFlow.lean`, but it still depends on real Jost-edge
membership and connectedness hypotheses that are not currently global facts.
The second option is the preferred theorem-2 surface, because it is exactly
what the sector-cover proof needs and it does not confuse PET connectivity
with fixed-fiber chamber connectivity.

Conditional BHW-side blocker after the OS edge supplier exists:

```lean
theorem BHW.extendF_pet_branch_independence_of_adjacent
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hAdj :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) →
        BHW.extendF F (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
          BHW.extendF F (fun k => z (π k))) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π →
      z ∈ BHW.permutedExtendedTubeSector d n ρ →
      BHW.extendF F (fun k => z (π k)) =
        BHW.extendF F (fun k => z (ρ k))
```

but the proof of this theorem must come from an explicit PET monodromy/Jost
edge package, not from `orbit_chamber_path_discretization`.  The proof docs
below refine the germ-chain version of that package as deferred BHW
infrastructure.

The BHW-phase documentation task, once the adjacent OS edge supplier is ready
in the relevant dimension range, is to make the germ-chain theorem fully
Lean-ready:

1. specify the prefix-union gluing data precisely enough that the generic
   analytic gluing proof is routine SCV/topology;
2. specify the BHW geometry theorem that produces such data for PET sector
   germs, using local Jost edge seeds with explicit `hV_ET`/`hV_permET`
   membership;
3. only after these two statements are stable should production Lean move past
   the already-checked conditional adapters.

This supersedes the earlier "preferred fixed-fiber target" language in this
section.  The fixed-fiber path is now a quarantined diagnostic route, not the
active theorem-2 implementation plan.

If the fixed-fiber theorem is not available, the fallback should be stated as
a genuine analytic-continuation theorem, not as a topology-only gluing lemma.
The correct abstraction is a chain of sector germs:

```lean
structure BHW.PETGermChain
    (d n : ℕ)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) where
  length : ℕ
  label : Fin (length + 1) → Equiv.Perm (Fin n)
  label_zero : label 0 = π
  label_last : label ⟨length, Nat.lt_succ_self length⟩ = ρ
  domain : (j : Fin (length + 1)) →
    Set (Fin n → Fin (d + 1) → ℂ)
  domain_open : ∀ j, IsOpen (domain j)
  domain_preconnected : ∀ j, IsPreconnected (domain j)
  domain_subset_sector :
    ∀ j, domain j ⊆ BHW.permutedExtendedTubeSector d n (label j)
  endpoint_mem_start : z ∈ domain 0
  endpoint_mem_last : z ∈ domain ⟨length, Nat.lt_succ_self length⟩
  adjacent_or_overlap :
    ∀ j : Fin length,
      let j0 : Fin (length + 1) := j.castSucc
      let j1 : Fin (length + 1) := j.succ
      (domain j0 ∩ domain j1).Nonempty ∧
      -- either the labels are equal, or they differ by one adjacent swap
      (label j0 = label j1 ∨
        ∃ (i : Fin n) (hi : i.val + 1 < n),
          label j1 = label j0 * Equiv.swap i ⟨i.val + 1, hi⟩)
```

This raw structure is still not enough by itself.  Pairwise consecutive overlap
control does not let Lean define one glued function on the growing union:
when adding `domain (j+1)`, the new domain may intersect earlier domains in
components not connected to the last adjacent overlap.  Therefore the
implementation theorem needs a cumulative-prefix condition, not merely
pairwise overlap connectedness:

```lean
def BHW.PETGermChain.prefixUnion
    (C : BHW.PETGermChain d n π ρ z)
    (j : Fin (C.length + 1)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ k : {k : Fin (C.length + 1) // k.val ≤ j.val}, C.domain k.1

prefix_inter_next_preconnected :
  ∀ j : Fin length,
    IsPreconnected
      (prefixUnion C j.castSucc ∩ C.domain j.succ)

prefix_inter_next_hits_adjacent_overlap :
  ∀ j : Fin length,
    (prefixUnion C j.castSucc ∩ C.domain j.succ ∩
      C.domain j.castSucc).Nonempty
```

The second condition says that the cumulative intersection contains a point in
the last consecutive overlap.  Since `hAdj` gives equality on the full adjacent
sector overlap, the old glued function and the new sector branch agree on a
nonempty open neighborhood inside this cumulative intersection.  The first
condition then lets the identity theorem propagate that equality across the
whole cumulative intersection, making the next gluing step well-defined.

The strong version yields an implementation theorem of the form:

```lean
theorem BHW.pet_branch_independence_of_germChain
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hG_holo :
      ∀ π, DifferentiableOn ℂ (G π) (BHW.permutedExtendedTubeSector d n π))
    (hAdj :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) →
        G (π * Equiv.swap i ⟨i.val + 1, hi⟩) z = G π z)
    (hChain :
      BHW.PETGermChainReady d n π ρ z) :
    G π z = G ρ z
```

The earlier three-argument form with separate `hPrefixPreconnected` and
`hPrefixHits` is logically equivalent, but the ready record is cleaner for
Lean: the chain data and the prefix-intersection data travel together.

An important implementation constraint: `PETGermChain` and
`PETGermChainReady` must be data-carrying types, not `Prop`-valued structures.
Their `length`, `label`, and `domain` fields are used to define
`prefixUnion` and `prefixValue`; putting the structures in `Prop` would create
proof-irrelevance/elimination problems and would be a bad Lean interface.

The proof would inductively glue a holomorphic function on the prefix union.
At step `j`, the new branch agrees with the prefix-glued function on the last
adjacent overlap by `hAdj`; the ready chain supplies a nonempty seed in the
cumulative intersection; prefix preconnectedness and the identity theorem
extend that equality to the whole cumulative intersection; then the usual
local piecewise definition is well-defined on the enlarged union.  This is
heavier than the fixed-fiber route and should not be implemented until the
exact chain/overlap theorem is mathematically specified.  At present the repo
has identity/connectivity tools, but no monodromy or germ API, so this fallback
is proof-doc work, not Lean-ready production work.

The older sketch was:

```lean
theorem BHW.pet_branch_independence_of_germChain_old_shape
    ...
    (hChain :
      BHW.PETGermChain d n π ρ z)
    (hPrefixPreconnected :
      ∀ j : Fin hChain.length,
        IsPreconnected
          (hChain.prefixUnion j.castSucc ∩ hChain.domain j.succ))
    (hPrefixHits :
      ∀ j : Fin hChain.length,
        (hChain.prefixUnion j.castSucc ∩ hChain.domain j.succ ∩
          hChain.domain j.castSucc).Nonempty) :
    G π z = G ρ z
```

To make the generic gluing theorem Lean-ready, split it into a purely formal
SCV/topology theorem and a separate BHW geometry theorem.

The formal theorem should use a strengthened chain record:

```lean
structure BHW.PETGermChainReady
    (d n : ℕ)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    extends BHW.PETGermChain d n π ρ z where
  prefix_inter_next_preconnected :
    ∀ j : Fin length,
      IsPreconnected
        (prefixUnion j.castSucc ∩ domain j.succ)
  prefix_inter_next_seed :
    ∀ j : Fin length,
      (prefixUnion j.castSucc ∩ domain j.succ ∩
        domain j.castSucc).Nonempty
```

The notation here is schematic: in Lean, `prefixUnion` should be defined as a
namespace function taking the base chain as an explicit argument, because a
structure cannot directly refer to a later namespace definition in an extends
field.  The intended production shape is:

```lean
def BHW.PETGermChain.prefixUnion
    (C : BHW.PETGermChain d n π ρ z)
    (j : Fin (C.length + 1)) :
    Set (Fin n → Fin (d + 1) → ℂ) := ...

structure BHW.PETGermChainReady ... where
  toChain : BHW.PETGermChain d n π ρ z
  prefix_inter_next_preconnected :
    ∀ j : Fin toChain.length,
      IsPreconnected
        (toChain.prefixUnion j.castSucc ∩ toChain.domain j.succ)
  prefix_inter_next_seed :
    ∀ j : Fin toChain.length,
      (toChain.prefixUnion j.castSucc ∩ toChain.domain j.succ ∩
        toChain.domain j.castSucc).Nonempty
```

The generic proof should then be implemented through the following helper
lemmas, all independent of OS/QFT:

```lean
theorem BHW.PETGermChain.prefixUnion_open
    (C : BHW.PETGermChain d n π ρ z)
    (j : Fin (C.length + 1)) :
    IsOpen (C.prefixUnion j)

theorem BHW.PETGermChain.prefixUnion_mem_of_domain_mem
    (C : BHW.PETGermChain d n π ρ z)
    {j k : Fin (C.length + 1)} (hkj : k.val ≤ j.val) :
    C.domain k ⊆ C.prefixUnion j

theorem BHW.branch_eq_on_consecutive_domain_overlap
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hAdj : ...)
    (C : BHW.PETGermChain d n π ρ z)
    (j : Fin C.length) :
    EqOn (G (C.label j.castSucc)) (G (C.label j.succ))
      (C.domain j.castSucc ∩ C.domain j.succ)
```

For the induction, define a prefix value on `C.prefixUnion j` by choosing any
domain in the prefix containing the point:

```lean
noncomputable def BHW.PETGermChain.prefixValue
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (C : BHW.PETGermChain d n π ρ z)
    (j : Fin (C.length + 1))
    (w : Fin n → Fin (d + 1) → ℂ) : ℂ := ...
```

The Lean-safe definition should be by classical choice from the prefix union:

```lean
noncomputable def BHW.PETGermChain.prefixWitness
    (C : BHW.PETGermChain d n π ρ z)
    (j : Fin (C.length + 1))
    (w : Fin n → Fin (d + 1) → ℂ)
    (hw : w ∈ C.prefixUnion j) :
    {k : Fin (C.length + 1) // k.val ≤ j.val ∧ w ∈ C.domain k} := ...

noncomputable def BHW.PETGermChain.prefixValue
    (G : (π : Equiv.Perm (Fin n)) →
      (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (C : BHW.PETGermChain d n π ρ z)
    (j : Fin (C.length + 1))
    (w : Fin n → Fin (d + 1) → ℂ) : ℂ :=
  if hw : w ∈ C.prefixUnion j then
    G (C.label ((C.prefixWitness j w hw).1)) w
  else
    0
```

This definition is allowed before well-definedness is known.  The proof of
well-definedness is exactly the prefix compatibility invariant:

```lean
theorem BHW.PETGermChain.prefixValue_eq_branch
    (G : ...)
    (hG_holo : ...)
    (hAdj : ...)
    (C : BHW.PETGermChainReady d n π ρ z)
    (j : Fin (C.toChain.length + 1))
    (k : Fin (C.toChain.length + 1))
    (hkj : k.val ≤ j.val) :
    EqOn (C.toChain.prefixValue G j) (G (C.toChain.label k))
      (C.toChain.domain k)
```

The formal gluing theorem should prove three invariants simultaneously by
induction on `j`:

```lean
theorem BHW.PETGermChain.prefixValue_eq_branch
theorem BHW.PETGermChain.prefixValue_holomorphicOn
theorem BHW.PETGermChain.prefixValue_extends_succ
```

with the following intended theorem shapes:

```lean
theorem BHW.PETGermChain.prefixValue_holomorphicOn
    (G : ...)
    (hG_holo : ...)
    (hAdj : ...)
    (C : BHW.PETGermChainReady d n π ρ z)
    (j : Fin (C.toChain.length + 1)) :
    DifferentiableOn ℂ (C.toChain.prefixValue G j)
      (C.toChain.prefixUnion j)

theorem BHW.PETGermChain.prefixValue_extends_succ
    (G : ...)
    (hG_holo : ...)
    (hAdj : ...)
    (C : BHW.PETGermChainReady d n π ρ z)
    (j : Fin C.toChain.length) :
    EqOn
      (C.toChain.prefixValue G j.castSucc)
      (G (C.toChain.label j.succ))
      (C.toChain.prefixUnion j.castSucc ∩ C.toChain.domain j.succ)
```

`prefixValue_holomorphicOn` follows from `prefixValue_eq_branch`: if
`w ∈ prefixUnion j`, choose a prefix domain `C.domain k` containing `w`.
Since `C.domain k` is open and `prefixValue G j = G (label k)` on that domain,
`prefixValue G j` is eventually equal to a holomorphic branch near `w`.

The induction step for `prefixValue_extends_succ` is the only analytic proof:

1. set

```lean
I_j := C.toChain.prefixUnion j.castSucc ∩ C.toChain.domain j.succ
```

2. prove `IsOpen I_j` from `prefixUnion_open` and `domain_open`;
3. use `prefix_inter_next_preconnected` as the preconnectedness input for the
   identity theorem;
4. use `prefix_inter_next_seed` to obtain a point in
   `domain j.castSucc ∩ domain j.succ`, where the old prefix value equals
   `G (label j.castSucc)` by the induction hypothesis and the new branch
   equals it by `branch_eq_on_consecutive_domain_overlap`;
5. because both `domain j.castSucc` and `domain j.succ` are open, this seed
   gives an `eventuallyEq` neighborhood inside `I_j`;
6. apply `SCV.identity_theorem_product` on `I_j` to prove the old prefix value
   and the new branch agree on all of `I_j`;
7. use this equality to extend the prefix compatibility invariant to
   `j.succ`.

The update from prefix `j` to prefix `j.succ` then splits into two cases for a
point `w ∈ prefixUnion j.succ`:

1. if `w ∈ prefixUnion j.castSucc`, use the old prefix compatibility theorem;
2. if `w ∈ domain j.succ`, use either the definition of `prefixValue` on the
   new domain or, on the overlap with the old prefix, the just-proved
   `prefixValue_extends_succ`.

This is the Lean step that prevents hidden monodromy assumptions: the only
place equality is propagated beyond the last adjacent overlap is the explicit
identity-theorem call on `I_j`.

After the final induction step, the target follows without another analytic
argument:

```lean
have hstart :
    C.toChain.prefixValue G last z = G π z :=
  -- `endpoint_mem_start`, `label_zero`, and `prefixValue_eq_branch`
have hend :
    C.toChain.prefixValue G last z = G ρ z :=
  -- `endpoint_mem_last`, `label_last`, and `prefixValue_eq_branch`
exact hstart.symm.trans hend
```

This generic theorem is a good small Lean target **only after** the geometry
theorem below is made precise enough to consume it:

```lean
theorem BHW.petGermChainReady_exists
    [NeZero d]
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    Nonempty (BHW.PETGermChainReady d n π ρ z)
```

This is the true BHW/PET monodromy geometry statement.  It must not be proved
by fixed-fiber reachable-label connectivity.  Its proof should construct a
finite sector-germ continuation chain in PET whose cumulative intersections
are preconnected and seeded by adjacent Jost/EOW overlaps.  The local real-edge
seeds must carry explicit `hV_ET` and `hV_permET` hypotheses.  They must not
rely on a global `BHW.JostSet → ExtendedTube` theorem for the current
`BHW.JostSet`, since the pairwise-spacelike definition is too broad for that
claim.

The cover-level construction of `petGermChainReady_exists` should be split into
two independent pieces.

First, a finite adjacent word from `π` to `ρ`.  This is purely combinatorial:

```lean
structure BHW.PETAdjacentLabelWord
    (n : ℕ)
    (π ρ : Equiv.Perm (Fin n)) where
  length : ℕ
  label : Fin (length + 1) → Equiv.Perm (Fin n)
  label_zero : label 0 = π
  label_last : label ⟨length, Nat.lt_succ_self length⟩ = ρ
  step :
    ∀ j : Fin length,
      ∃ (i : Fin n) (hi : i.val + 1 < n),
        label j.succ = label j.castSucc * Equiv.swap i ⟨i.val + 1, hi⟩
```

Existence follows from adjacent transpositions generating `Equiv.Perm (Fin n)`,
using the same induction principle already used in
`PermutedTubeConnected.lean`:

```lean
theorem BHW.petAdjacentLabelWord_exists
    (π ρ : Equiv.Perm (Fin n)) :
    Nonempty (BHW.PETAdjacentLabelWord n π ρ)
```

Second, choose analytic channel domains for that word.  The transition seeds
are **not required to be the endpoint `z`**; this is the key distinction from
the false fixed-fiber route.  For each adjacent step, use adjacent sector
overlap nonemptiness to choose a point

```lean
q_j ∈ S (label j.castSucc) ∩ S (label j.succ).
```

Then choose an open preconnected channel domain inside each sector that links
the previous transition seed to the next transition seed.  At the ends, the
channels must also contain the target point `z`:

```lean
structure BHW.PETGermChannelData
    (d n : ℕ)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (W : BHW.PETAdjacentLabelWord n π ρ) where
  transition :
    (j : Fin W.length) → Fin n → Fin (d + 1) → ℂ
  transition_mem_left :
    ∀ j : Fin W.length,
      transition j ∈ BHW.permutedExtendedTubeSector d n (W.label j.castSucc)
  transition_mem_right :
    ∀ j : Fin W.length,
      transition j ∈ BHW.permutedExtendedTubeSector d n (W.label j.succ)
  domain :
    (j : Fin (W.length + 1)) → Set (Fin n → Fin (d + 1) → ℂ)
  domain_open : ∀ j, IsOpen (domain j)
  domain_preconnected : ∀ j, IsPreconnected (domain j)
  domain_subset_sector :
    ∀ j, domain j ⊆ BHW.permutedExtendedTubeSector d n (W.label j)
  start_mem : z ∈ domain 0
  last_mem : z ∈ domain ⟨W.length, Nat.lt_succ_self W.length⟩
  transition_mem_prev_domain :
    ∀ j : Fin W.length, transition j ∈ domain j.castSucc
  transition_mem_next_domain :
    ∀ j : Fin W.length, transition j ∈ domain j.succ
```

Define its prefix union exactly as for `PETGermChain`:

```lean
def BHW.PETGermChannelData.prefixUnion
    (C : BHW.PETGermChannelData d n π ρ z W)
    (j : Fin (W.length + 1)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ k : {k : Fin (W.length + 1) // k.val ≤ j.val}, C.domain k.1
```

This channel data is still not enough for Lean gluing, because a new channel
can intersect the earlier prefix in extra components not connected to the last
transition seed.  The ready data must include the cumulative-intersection
conditions from `PETGermChainReady`:

```lean
structure BHW.PETGermChannelData.Ready
    (C : BHW.PETGermChannelData d n π ρ z W) : Prop where
  prefix_inter_next_preconnected :
    ∀ j : Fin W.length,
      IsPreconnected
        (C.prefixUnion j.castSucc ∩ C.domain j.succ)
  prefix_inter_next_seed :
    ∀ j : Fin W.length,
      C.transition j ∈
        C.prefixUnion j.castSucc ∩ C.domain j.succ ∩ C.domain j.castSucc
```

These conditions are precisely what converts cover-level adjacent equality
into global branch equality.  They are also the place where the remaining BHW
geometry lives.  In prose, the missing geometry theorem is:

```lean
theorem BHW.petGermChannelData_exists
    [NeZero d]
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ)
    (W : BHW.PETAdjacentLabelWord n π ρ) :
    ∃ C : BHW.PETGermChannelData d n π ρ z W,
      -- the cumulative prefix intersections are preconnected and hit
      -- the prescribed adjacent transition seeds
      BHW.PETGermChannelData.Ready C
```

The conversion from channel data to the generic germ-chain record is direct:

```lean
def BHW.PETGermChannelData.toPETGermChain
    (C : BHW.PETGermChannelData d n π ρ z W) :
    BHW.PETGermChain d n π ρ z where
  length := W.length
  label := W.label
  label_zero := W.label_zero
  label_last := W.label_last
  domain := C.domain
  domain_open := C.domain_open
  domain_preconnected := C.domain_preconnected
  domain_subset_sector := C.domain_subset_sector
  endpoint_mem_start := C.start_mem
  endpoint_mem_last := C.last_mem
  adjacent_or_overlap := by
    intro j
    refine ⟨⟨C.transition j, C.transition_mem_prev_domain j,
      C.transition_mem_next_domain j⟩, Or.inr ?_⟩
    exact W.step j

def BHW.PETGermChannelData.toPETGermChainReady
    (C : BHW.PETGermChannelData d n π ρ z W)
    (hC : BHW.PETGermChannelData.Ready C) :
    BHW.PETGermChainReady d n π ρ z where
  toChain := C.toPETGermChain
  prefix_inter_next_preconnected := by
    -- identify `C.prefixUnion` with `C.toPETGermChain.prefixUnion`
    simpa [BHW.PETGermChannelData.toPETGermChain,
      BHW.PETGermChannelData.prefixUnion,
      BHW.PETGermChain.prefixUnion] using hC.prefix_inter_next_preconnected
  prefix_inter_next_seed := by
    -- same prefix-union identification
    simpa [BHW.PETGermChannelData.toPETGermChain,
      BHW.PETGermChannelData.prefixUnion,
      BHW.PETGermChain.prefixUnion] using hC.prefix_inter_next_seed
```

This theorem may be proved by constructing small "tubes" inside the
preconnected open sectors connecting endpoint/transition points while
controlling overlaps with the previous prefix.  That is genuine complex-domain
geometry.  It is weaker than fixed-fiber chamber connectivity because the
transition points may move in PET, but it is stronger than bare PET
connectedness because it controls the prefix intersections used by the
identity theorem.

Once `petAdjacentLabelWord_exists` and `petGermChannelData_exists` are proved,
`petGermChainReady_exists` is just packaging:

```lean
theorem BHW.petGermChainReady_exists
    [NeZero d]
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    Nonempty (BHW.PETGermChainReady d n π ρ z) := by
  obtain ⟨W⟩ := BHW.petAdjacentLabelWord_exists π ρ
  obtain ⟨C, hCready⟩ :=
    BHW.petGermChannelData_exists π ρ z hzπ hzρ W
  exact ⟨C.toPETGermChainReady hCready⟩
```

The proof of `petGermChannelData_exists` should itself be decomposed rather
than left as a black box.  The following geometry lemmas are the intended
subtargets.

First, each explicit sector should be path connected.  The repo already has
preconnectedness:

```lean
theorem BHW.permutedExtendedTubeSector_isPreconnected
```

Since sectors are open subsets of a finite-dimensional complex vector space,
path connectedness should follow from local path-connectedness:

```lean
theorem BHW.permutedExtendedTubeSector_pathConnected
    [NeZero d]
    (π : Equiv.Perm (Fin n)) :
    IsPathConnected (BHW.permutedExtendedTubeSector d n π)
```

If the exact Mathlib theorem is inconvenient, use the weaker path-existence
form needed by the construction:

```lean
theorem BHW.exists_path_in_permutedExtendedTubeSector
    [NeZero d]
    (π : Equiv.Perm (Fin n))
    {a b : Fin n → Fin (d + 1) → ℂ}
    (ha : a ∈ BHW.permutedExtendedTubeSector d n π)
    (hb : b ∈ BHW.permutedExtendedTubeSector d n π) :
    ∃ γ : C( unitInterval, Fin n → Fin (d + 1) → ℂ),
      γ 0 = a ∧ γ 1 = b ∧
      ∀ t, γ t ∈ BHW.permutedExtendedTubeSector d n π
```

Second, a compact path inside an open set should have a connected open tube
inside that open set:

```lean
theorem BHW.exists_open_preconnected_tube_around_path
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    {U : Set E} (hU_open : IsOpen U)
    {γ : C(unitInterval, E)}
    (hγU : ∀ t, γ t ∈ U) :
    ∃ D : Set E,
      IsOpen D ∧ IsPreconnected D ∧
      Set.range γ ⊆ D ∧ D ⊆ U
```

This is a standard compactness/Lebesgue-number argument: cover the compact path
image by balls contained in `U`; extract a finite chain of overlapping balls
along a subdivision of the path; take their union.  The union is open and
preconnected because consecutive balls overlap.

Together these give an uncontrolled sector channel:

```lean
theorem BHW.exists_sector_channel
    [NeZero d]
    (π : Equiv.Perm (Fin n))
    {a b : Fin n → Fin (d + 1) → ℂ}
    (ha : a ∈ BHW.permutedExtendedTubeSector d n π)
    (hb : b ∈ BHW.permutedExtendedTubeSector d n π) :
    ∃ D : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen D ∧ IsPreconnected D ∧
      D ⊆ BHW.permutedExtendedTubeSector d n π ∧
      a ∈ D ∧ b ∈ D
```

This uncontrolled channel is not sufficient for `Ready`; it does not control
how the new channel intersects the previous prefix.  The controlled extension
theorem needed for the induction must be **prefix-specific**.  It should not be
implemented as a blanket theorem for arbitrary open `P`, since an arbitrary
open set can intersect a new channel in many disconnected components.  The
production theorem should take a partial ready channel prefix as input, carrying
whatever tameness/separation data the construction maintains.

The schematic shape is:

```lean
theorem BHW.exists_controlled_sector_channel_for_ready_prefix
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    -- In production, replace these schematic `P`, `Dprev`, and hypotheses by
    -- a partial `PETGermChannelData` prefix whose maintained invariants imply
    -- the displayed conditions.
    (P Dprev : Set (Fin n → Fin (d + 1) → ℂ))
    (hP_open : IsOpen P)
    (hDprev_open : IsOpen Dprev)
    {qprev qnext : Fin n → Fin (d + 1) → ℂ}
    (hqprevP : qprev ∈ P)
    (hqprevDprev : qprev ∈ Dprev)
    (hqprevσ : qprev ∈ BHW.permutedExtendedTubeSector d n σ)
    (hqnextσ : qnext ∈ BHW.permutedExtendedTubeSector d n σ) :
    ∃ D : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen D ∧ IsPreconnected D ∧
      D ⊆ BHW.permutedExtendedTubeSector d n σ ∧
      qprev ∈ D ∧ qnext ∈ D ∧
      IsPreconnected (P ∩ D) ∧
      qprev ∈ P ∩ D ∩ Dprev
```

This theorem is the current genuine geometric sub-blocker.  It says: given the
already-glued controlled prefix `P`, the previous channel `Dprev`, the
transition seed `qprev` where the old and new branches already agree, and the
next transition seed `qnext`, choose the next channel `D` inside the current
sector so that `P ∩ D` is a single preconnected region hit by `qprev`.

If this controlled-prefix theorem is still too strong, the `Ready` record
should be weakened or replaced by a Riemann-domain monodromy theorem.  What
must not happen is to silently replace it by bare sector preconnectedness or
PET connectedness.  Those facts do not control `P ∩ D`.

To make the prefix-specific version Lean-shaped, preselect all adjacent
transition seeds and then build domains one at a time.

```lean
structure BHW.PETGermTransitionPlan
    (d n : ℕ)
    (π ρ : Equiv.Perm (Fin n))
    (W : BHW.PETAdjacentLabelWord n π ρ) where
  transition :
    (j : Fin W.length) → Fin n → Fin (d + 1) → ℂ
  transition_mem_left :
    ∀ j : Fin W.length,
      transition j ∈ BHW.permutedExtendedTubeSector d n (W.label j.castSucc)
  transition_mem_right :
    ∀ j : Fin W.length,
      transition j ∈ BHW.permutedExtendedTubeSector d n (W.label j.succ)
```

Existence is a finite choice over adjacent overlap nonemptiness:

```lean
theorem BHW.petGermTransitionPlan_exists
    [NeZero d]
    (W : BHW.PETAdjacentLabelWord n π ρ) :
    Nonempty (BHW.PETGermTransitionPlan d n π ρ W)
```

For prefix indexing, define the two casts once:

```lean
def BHW.PETAdjacentLabelWord.prefixIndex
    (W : BHW.PETAdjacentLabelWord n π ρ)
    {r : ℕ} (hr : r ≤ W.length)
    (j : Fin (r + 1)) : Fin (W.length + 1) :=
  ⟨j.val, by
    -- `j.val ≤ r ≤ W.length`, hence `j.val < W.length + 1`
    omega⟩

def BHW.PETAdjacentLabelWord.prefixStepIndex
    (W : BHW.PETAdjacentLabelWord n π ρ)
    {r : ℕ} (hr : r ≤ W.length)
    (j : Fin r) : Fin W.length :=
  ⟨j.val, by
    -- `j.val < r ≤ W.length`
    omega⟩
```

Then the partial ready prefix should be a data-carrying structure:

```lean
structure BHW.PETGermChannelPrefix
    (d n : ℕ)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (W : BHW.PETAdjacentLabelWord n π ρ)
    (T : BHW.PETGermTransitionPlan d n π ρ W)
    (r : ℕ) (hr : r ≤ W.length) where
  domain :
    (j : Fin (r + 1)) → Set (Fin n → Fin (d + 1) → ℂ)
  domain_open : ∀ j, IsOpen (domain j)
  domain_preconnected : ∀ j, IsPreconnected (domain j)
  domain_subset_sector :
    ∀ j, domain j ⊆
      BHW.permutedExtendedTubeSector d n
        (W.label (W.prefixIndex hr j))
  start_mem : z ∈ domain 0
  transition_mem_prev :
    ∀ j : Fin r,
      T.transition (W.prefixStepIndex hr j) ∈ domain j.castSucc
  transition_mem_next :
    ∀ j : Fin r,
      T.transition (W.prefixStepIndex hr j) ∈ domain j.succ
  outgoing_mem :
    ∀ h : r < W.length,
      T.transition ⟨r, h⟩ ∈ domain ⟨r, Nat.lt_succ_self r⟩
  final_mem :
    r = W.length → z ∈ domain ⟨r, Nat.lt_succ_self r⟩
```

The `outgoing_mem` field is the key bookkeeping point.  A prefix ending at
label `r` already contains the transition seed to the next label when such a
next label exists.  Therefore the one-step extension has a seed in the old
prefix intersection.

The prefix union for a partial prefix is:

```lean
def BHW.PETGermChannelPrefix.prefixUnion
    (P : BHW.PETGermChannelPrefix d n π ρ z W T r hr)
    (j : Fin (r + 1)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ k : {k : Fin (r + 1) // k.val ≤ j.val}, P.domain k.1
```

The ready-prefix conditions are:

```lean
structure BHW.PETGermChannelPrefix.Ready
    (P : BHW.PETGermChannelPrefix d n π ρ z W T r hr) : Prop where
  prefix_inter_next_preconnected :
    ∀ j : Fin r,
      IsPreconnected
        (P.prefixUnion j.castSucc ∩ P.domain j.succ)
  prefix_inter_next_seed :
    ∀ j : Fin r,
      T.transition (W.prefixStepIndex hr j) ∈
        P.prefixUnion j.castSucc ∩ P.domain j.succ ∩ P.domain j.castSucc
```

The one-step extension theorem should now be stated against this prefix record,
not against arbitrary open sets:

```lean
theorem BHW.PETGermChannelPrefix.extend_one
    [NeZero d]
    {r : ℕ} {hr : r ≤ W.length}
    (P : BHW.PETGermChannelPrefix d n π ρ z W T r hr)
    (hP : BHW.PETGermChannelPrefix.Ready P)
    (hrlt : r < W.length) :
    ∃ P' : BHW.PETGermChannelPrefix d n π ρ z W T (r + 1)
        (Nat.succ_le_of_lt hrlt),
      BHW.PETGermChannelPrefix.Ready P' ∧
      -- `P'` restricts to `P` on the first `r + 1` domains.
      BHW.PETGermChannelPrefix.Extends P P'
```

Here `Extends` should be a small equality-on-prefix relation:

```lean
def BHW.PETGermChannelPrefix.Extends
    (P : BHW.PETGermChannelPrefix d n π ρ z W T r hr)
    (P' : BHW.PETGermChannelPrefix d n π ρ z W T (r + 1) hr')
    : Prop :=
  ∀ j : Fin (r + 1),
    P'.domain j.castSucc = P.domain j
```

The proof of `extend_one` is exactly the controlled-channel geometry.  Let

```lean
qprev := T.transition ⟨r, hrlt⟩
qnext :=
  if hnext : r + 1 < W.length then
    T.transition ⟨r + 1, hnext⟩
  else
    z
```

Use `P.outgoing_mem hrlt` to know `qprev ∈ P.domain last`, hence
`qprev ∈ P.prefixUnion last`.  Then construct a new domain `D` inside
`S (W.label (r+1))` containing `qprev` and `qnext`, with
`P.prefixUnion last ∩ D` preconnected and containing `qprev`.  Append `D` as
the new last domain.  The new `outgoing_mem` is supplied by `qnext` when
`hnext` holds; the new `final_mem` is supplied by `qnext = z` in the final
case.

This makes the remaining sub-blocker completely explicit:

```lean
theorem BHW.PETGermChannelPrefix.exists_extend_domain
    [NeZero d]
    {r : ℕ} {hr : r ≤ W.length}
    (P : BHW.PETGermChannelPrefix d n π ρ z W T r hr)
    (hP : BHW.PETGermChannelPrefix.Ready P)
    (hrlt : r < W.length) :
    ∃ D : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen D ∧
      IsPreconnected D ∧
      D ⊆ BHW.permutedExtendedTubeSector d n
        (W.label ⟨r + 1, Nat.succ_lt_succ hrlt⟩) ∧
      T.transition ⟨r, hrlt⟩ ∈ D ∧
      (if hnext : r + 1 < W.length then
          T.transition ⟨r + 1, hnext⟩ ∈ D
        else
          z ∈ D) ∧
      IsPreconnected
        (P.prefixUnion ⟨r, Nat.lt_succ_self r⟩ ∩ D) ∧
      T.transition ⟨r, hrlt⟩ ∈
        P.prefixUnion ⟨r, Nat.lt_succ_self r⟩ ∩
          D ∩ P.domain ⟨r, Nat.lt_succ_self r⟩
```

If `exists_extend_domain` cannot be proved for the maintained prefix invariant
above, the channel-domain route should be abandoned in favor of a direct
Riemann-domain monodromy theorem.

A sufficient path-level theorem for `exists_extend_domain` is:

```lean
theorem BHW.exists_sector_path_with_controlled_prefix_intersection
    [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (P Dprev : Set (Fin n → Fin (d + 1) → ℂ))
    (hP_open : IsOpen P)
    (hDprev_open : IsOpen Dprev)
    {qprev qnext : Fin n → Fin (d + 1) → ℂ}
    (hqprevP : qprev ∈ P)
    (hqprevDprev : qprev ∈ Dprev)
    (hqprevσ : qprev ∈ BHW.permutedExtendedTubeSector d n σ)
    (hqnextσ : qnext ∈ BHW.permutedExtendedTubeSector d n σ) :
    ∃ γ : C(unitInterval, Fin n → Fin (d + 1) → ℂ),
      γ 0 = qprev ∧ γ 1 = qnext ∧
      (∀ t, γ t ∈ BHW.permutedExtendedTubeSector d n σ) ∧
      ∃ D : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen D ∧ IsPreconnected D ∧
        Set.range γ ⊆ D ∧
        D ⊆ BHW.permutedExtendedTubeSector d n σ ∧
        IsPreconnected (P ∩ D) ∧
        qprev ∈ P ∩ D ∩ Dprev
```

This statement says the path can be thickened to an open preconnected tube
whose intersection with the existing prefix is still preconnected.  It is
exactly the nontrivial topological control missing from the bare sector
path-connectedness theorem.

At present this path-control theorem is **not** established.  It may require
extra maintained invariants, for example relatively compact channel closures,
a tree-like prefix construction, or an avoidance lemma saying the new path can
avoid the old prefix except near `qprev`.  If such invariants are needed, add
them to `PETGermChannelPrefix`; do not prove a false arbitrary-open-set
version.

With `initial_prefix` and `extend_one`, `petGermChannelData_exists` is an
ordinary finite induction over `r ≤ W.length`:

```lean
theorem BHW.PETGermChannelPrefix.initial
    [NeZero d]
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ)
    (W : BHW.PETAdjacentLabelWord n π ρ)
    (T : BHW.PETGermTransitionPlan d n π ρ W) :
    ∃ P0 : BHW.PETGermChannelPrefix d n π ρ z W T 0
        (Nat.zero_le W.length),
      BHW.PETGermChannelPrefix.Ready P0
```

The initial proof splits on `W.length = 0`.

1. If `W.length = 0`, then `W.label 0 = π = ρ`, and one channel inside `S π`
   containing `z` gives both `start_mem` and `final_mem`.
2. If `0 < W.length`, use `exists_sector_channel` in `S (W.label 0)` to
   connect `z` to `T.transition 0`.  This supplies `start_mem` and
   `outgoing_mem`; there are no prefix-intersection obligations for `r = 0`.

Then iterate:

```lean
theorem BHW.PETGermChannelPrefix.exists_full
    [NeZero d]
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ)
    (W : BHW.PETAdjacentLabelWord n π ρ)
    (T : BHW.PETGermTransitionPlan d n π ρ W) :
    ∃ P : BHW.PETGermChannelPrefix d n π ρ z W T W.length
        (le_rfl),
      BHW.PETGermChannelPrefix.Ready P
```

The proof is induction on `r` from `0` to `W.length`, applying
`extend_one` whenever `r < W.length`.  At the final prefix, `final_mem`
supplies `z ∈ domain last`, and `Ready P` supplies all cumulative
prefix-intersection conditions.

Finally convert the full prefix into `PETGermChannelData` by reusing its
domains and the preselected transition plan:

```lean
def BHW.PETGermChannelPrefix.toChannelData
    (P : BHW.PETGermChannelPrefix d n π ρ z W T W.length le_rfl) :
    BHW.PETGermChannelData d n π ρ z W := ...

theorem BHW.PETGermChannelPrefix.toChannelData_ready
    (P : BHW.PETGermChannelPrefix d n π ρ z W T W.length le_rfl)
    (hP : BHW.PETGermChannelPrefix.Ready P) :
    BHW.PETGermChannelData.Ready (P.toChannelData) := ...
```

At the current frontier, the formal gluing theorem is close to Lean-ready, but
`BHW.petGermChainReady_exists` is not.  That geometry theorem is the next
proof-doc gap to fill before production implementation should resume.

There is one more planning gate before committing to a global
`petGermChainReady_exists` proof.  The theorem-2 consumer is locality, i.e. an
adjacent spacelike interchange after suitable ordering/localization.  The repo
already has the adjacent-overlap theorem

```lean
theorem bvt_F_extendF_adjacent_overlap_of_selectedEdgeData
```

and the selected-branch adjacent compatibility theorem

```lean
theorem bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
```

Both consume `SelectedAdjacentPermutationEdgeData`, whose real-edge witness
already carries explicit `hV_ET` and `hV_permET`.  Therefore the next
proof-doc step must decide whether theorem 2 can be closed by a **direct
adjacent boundary/locality route** using these adjacent overlap equalities.  If
so, the global PET all-branch monodromy theorem is unnecessary for the current
closure and should remain future infrastructure.

Only if the live downstream consumer truly needs a symmetric scalar on all of
PET should we continue with the global monodromy theorem
`BHW.petGermChainReady_exists`.  In that case it must be documented as a
standard BHW monodromy theorem or through a stronger, correctly defined
tube-Jost set, not through the current pairwise-spacelike `BHW.JostSet` and not
through fixed-fiber chamber connectivity.

#### Current Gate A after the #1061 correction

The corrected Gate A is a cover-level classical-germ theorem, not a
fixed-fiber chain theorem and not a direct application of PET connectedness.
The tempting shortcut

```text
adjacent overlaps + connected PET + identity theorem
```

is incomplete because each branch `G π` is holomorphic on its own sector
`S π`, and the difference `G π - G ρ` is holomorphic only on
`S π ∩ S ρ`.  Adjacent equality along a decomposition of `π⁻¹ * ρ` provides
seeds in adjacent overlaps along the chain, not automatically in the final
two-sector overlap containing the target point `z`.

Thus the Lean-facing theorem must explicitly encode analytic continuation
through a cover of germs.  The acceptable proof routes are:

1. a data-carrying `PETGermChainReady` theorem whose prefix intersections are
   preconnected and seeded by adjacent overlaps;
2. an equivalent Riemann-domain single-valuedness theorem for the adjacent
   glued sector cover;
3. a stronger, correctly defined tube-Jost theorem whose hypotheses imply the
   required germ-chain data.

The unacceptable routes are:

1. fixed-fiber/reachable-label/orbit-chamber connectivity without a new proof;
2. global `BHW.JostSet → ⋂π S π`, which is false for the current
   pairwise-spacelike `BHW.JostSet`;
3. citing `BHW.isConnected_permutedExtendedTube` without giving branch
   holomorphy and equality on a single connected domain.

The next proof-doc obligation is therefore to make the first route
implementation-ready: define exactly what `PETGermChainReady` supplies, prove
the formal analytic gluing theorem from that data, and only then specialize it
to selected OS branches.

The correct theorem should be formulated at the level of analytic branches on
open sectors.  Write

```lean
S π := BHW.permutedExtendedTubeSector d n π
G π := bvt_selectedPETBranch OS lgc n π
```

The current production facts give:

1. `IsOpen (S π)`;
2. `IsPreconnected (S π)`;
3. `BHW.PermutedExtendedTube d n = ⋃ π, S π`;
4. `DifferentiableOn ℂ (G π) (S π)`;
5. `G (π * τ) = G π` on `S π ∩ S (π * τ)` for every adjacent swap `τ`;
6. `S π ∩ S (π * τ)` is nonempty for every adjacent swap `τ`.

These six facts still do not imply all-overlap compatibility for an arbitrary
finite open cover.  A tempting additional statement would be:

```lean
-- Do not adopt this as a target without a separate proof.
theorem BHW.petSector_pathSaturation_inter_next_preconnected ...
```

meaning that, for an adjacent path list `L` ending at `α` and a neighboring
sector `β`, every connected component of
`(⋃ π ∈ L, S π) ∩ S β` meets `S α ∩ S β`.  This would make an inductive
path-gluing proof straightforward, because equality on the last adjacent
overlap could be propagated to all of the new intersection by the identity
theorem.

But this path-saturation statement is itself a strong global geometry claim and
should be treated as unproved and possibly false until established from BHW
geometry.  It is not a safe next Lean target.  The production route should
instead expose the actual BHW monodromy / well-definedness theorem:

```lean
theorem BHW.extendF_pet_branch_independence_of_adjacent
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hAdj :
      ∀ (π : Equiv.Perm (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n
          (π * Equiv.swap i ⟨i.val + 1, hi⟩) →
        BHW.extendF F (fun k => z ((π * Equiv.swap i ⟨i.val + 1, hi⟩) k)) =
          BHW.extendF F (fun k => z (π k))) :
    ∀ (π ρ : Equiv.Perm (Fin n))
      (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ BHW.permutedExtendedTubeSector d n π →
      z ∈ BHW.permutedExtendedTubeSector d n ρ →
      BHW.extendF F (fun k => z (π k)) =
        BHW.extendF F (fun k => z (ρ k))
```

This theorem is not a wrapper: it is the hard single-valued analytic
continuation statement for the PET sector cover.  It is the selected-data
analogue of the older private `fullExtendF_well_defined` spine in
`BHWPermutation/PermutationFlow.lean`, but it must not consume
`IsLocallyCommutativeWeak d (bvt_W OS lgc)` or any theorem equivalent to the
public locality conclusion.

The proof obligations for this theorem are:

1. construct the analytic continuation space from the disjoint union of sector
   charts `Σ π, S π`, identifying adjacent charts on the full adjacent overlaps
   where `hAdj` gives equality;
2. prove the projection of this continuation space to
   `BHW.PermutedExtendedTube d n` is single-valued, or equivalently that the
   value of `BHW.extendF F` is constant on every fiber over a PET point;
3. prove this single-valuedness by the standard BHW monodromy argument, using
   adjacent swaps as the local edge-of-the-wedge seeds and the connected PET
   continuation domain, not by requiring a fixed point to remain in all
   intermediate absolute ET overlaps;
4. explicitly handle the low-dimensional branch (`d = 1`) if the available BHW
   geometry splits by dimension, as the existing `PermutationFlow` scaffolding
   does;
5. after single-valuedness is proved, define the PET scalar and use the already
   checked formal gluing adapter only as the final value-selection mechanism.

Once `BHW.extendF_pet_branch_independence_of_adjacent` exists, the algebraic
tail can follow the existing private `fullExtendF_well_defined` proof almost
verbatim, but with no `W` and no `hF_local_dist`.  The intermediate theorem
should be:

```lean
theorem BHW.F_permutation_invariance_of_petBranchIndependence
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hPET :
      ∀ (π ρ : Equiv.Perm (Fin n))
        (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ BHW.permutedExtendedTubeSector d n π →
        z ∈ BHW.permutedExtendedTubeSector d n ρ →
        BHW.extendF F (fun k => z (π k)) =
          BHW.extendF F (fun k => z (ρ k))) :
    ∀ {w : Fin n → Fin (d + 1) → ℂ}, w ∈ BHW.ForwardTube d n →
      ∀ {τ : Equiv.Perm (Fin n)} {Γ : ComplexLorentzGroup d},
        BHW.complexLorentzAction Γ (fun k => w (τ k)) ∈
          BHW.ForwardTube d n →
        F (BHW.complexLorentzAction Γ (fun k => w (τ k))) = F w
```

This theorem has now been implemented in
`Connectedness/PermutedTubeMonodromy.lean`.  The checked Lean proof factors
through the public reduction
`BHW.permutation_invariance_of_extendF_on_extendedTube`; the extra adapter

```lean
theorem BHW.extendF_perm_eq_on_extendedTube_of_petBranchIndependence
```

turns the all-sector `hPET` statement into the precise extended-tube
permutation hypothesis expected by that reduction.

Equivalent direct proof sketch:

1. set `z := BHW.complexLorentzAction Γ (fun k => w (τ k))`;
2. `z ∈ S 1` because the hypothesis says `z ∈ ForwardTube`, hence `z ∈ ET`;
3. `z ∈ S τ⁻¹` because `fun k => z (τ⁻¹ k) = BHW.complexLorentzAction Γ w`,
   and `BHW.complexLorentzAction Γ w ∈ ET` since `w ∈ ForwardTube ⊆ ET`;
4. apply `hPET 1 τ⁻¹ z` to get
   `BHW.extendF F z = BHW.extendF F (BHW.complexLorentzAction Γ w)`;
5. rewrite the left side by `BHW.extendF_eq_on_forwardTube`;
6. rewrite the right side by `BHW.extendF_complex_lorentz_invariant` and
   `BHW.extendF_eq_on_forwardTube`.

Then the existing `fullExtendF_well_defined` algebra becomes:

```lean
theorem BHW.fullExtendF_well_defined_of_petBranchIndependence
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (BHW.ForwardTube d n))
    (hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hPET : -- branch independence as above)
    {w₁ w₂ : Fin n → Fin (d + 1) → ℂ}
    (hw₁ : w₁ ∈ BHW.ForwardTube d n)
    (hw₂ : w₂ ∈ BHW.ForwardTube d n)
    {π₁ π₂ : Equiv.Perm (Fin n)} {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : BHW.complexLorentzAction Λ₁ (fun k => w₁ (π₁ k)) =
         BHW.complexLorentzAction Λ₂ (fun k => w₂ (π₂ k))) :
    F w₁ = F w₂
```

This theorem has also been implemented in
`Connectedness/PermutedTubeMonodromy.lean`.  The proof is the existing private
proof with the call to
`F_permutation_invariance` replaced by
`F_permutation_invariance_of_petBranchIndependence`.

An equivalent theorem shape is also acceptable if it is closer to the existing
private code:

```lean
theorem BHW.fullExtendF_well_defined_of_adjacentBranchEquality
    -- same analytic inputs and adjacent branch equality as above
    -- any two PET representations of the same point give the same `F` value
```

This version would let the existing `fullExtendF` construction be reused
non-circularly.  The key requirement is the same: the theorem must prove
single-valued PET analytic continuation from adjacent branch equality, not
assume all-permutation real edge data and not assume global Wightman locality.

Only after one of these BHW monodromy / well-definedness statements is proved
should the selected theorem be implemented:

```lean
theorem bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    bvt_selectedPETBranch OS lgc n π z =
      bvt_selectedPETBranch OS lgc n ρ z
```

by instantiating `G` with `bvt_selectedPETBranch OS lgc n`, `hG_holo` with
`bvt_selectedPETBranch_holomorphicOn_sector`, and `hAdj` with
`bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`.

This is the next proof-doc completion target.  Production Lean should not add a
theorem named `bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData` until
the single-valued PET monodromy / well-definedness theorem above is proved.

There is also an explicitly overstrong conditional helper:

```lean
structure SelectedAllPermutationEdgeData
theorem bvt_F_extendF_perm_overlap_of_selectedEdgeData
```

This all-permutation helper should not be treated as the OS-route construction
target.  It is retained only to keep the checked conditional branch-gluing
lemmas available while the real adjacent-to-general chain theorem is developed.
Under that overstrong hypothesis, value-level branch gluing has been checked:

```lean
noncomputable def bvt_selectedAbsolutePETGluedValue
theorem bvt_selectedAbsolutePETGluedValue_eq_extendF_perm
theorem bvt_selectedAbsolutePETGluedValue_eq_bvt_F_on_forwardTube
theorem bvt_selectedAbsolutePETGluedValue_holomorphicOn_PET
theorem bvt_selectedAbsolutePETGluedValue_lorentzInvariant
theorem bvt_selectedAbsolutePETGluedValue_permInvariant
```

This conditional package proves what the final adjacent-chain package must
recover: the selected branch value is independent of the chosen permutation
branch, agrees with `bvt_F OS lgc n` on the original forward tube, is
holomorphic on PET, and has the expected absolute Lorentz and finite-permutation
invariance on PET.  The missing theorem is now the honest one:

```lean
theorem bvt_selectedAbsolutePETGluedValue_eq_extendF_perm_of_adjacentEdgeData
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hπz : (fun k => z (π k)) ∈ BHW.ExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue OS lgc n z =
      BHW.extendF (bvt_F OS lgc n) (fun k => z (π k))
```

It must be proved by chaining adjacent-swap branch equalities through the PET
sector graph, not by requiring real edge data for `π₀⁻¹ * π` directly.

The remaining implementation work inside
`bvt_selectedReducedBHWExtensionData_exists` is therefore:

1. prove adjacent-to-general PET branch gluing from
   `SelectedAdjacentPermutationEdgeData`;
2. prove the glued absolute PET scalar is constant on uniform-translation
   fibers wherever the two representatives lie in PET;
3. descend the glued absolute PET scalar through `BHW.reducedDiffMap` to the
   image domain `BHW.ReducedPermutedExtendedTubeN d m`;
4. prove the descended function agrees with
   `(bvt_selectedReducedForwardTubeInput OS lgc χ m).toFun` on
   `BHW.ReducedForwardTubeN d m`, and transport the already-proved absolute
   Lorentz/permutation invariance to the reduced invariance fields required by
   `BHW.ReducedBHWExtensionData`;
5. feed the resulting `Fred` to
   `bvt_selectedPETExtensionOfReducedData`.

#### Next quotient-descent seam: selected translation-fiber constancy

The next theorem is not yet a Lean-ready one-liner.  The exact mathematical
surface needed before reduced descent is:

```lean
theorem bvt_selectedAbsolutePETGluedValue_translationInvariant_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ BHW.PermutedExtendedTube d n) :
    bvt_selectedAbsolutePETGluedValue OS lgc n
        (fun k μ => z k μ + c μ) =
      bvt_selectedAbsolutePETGluedValue OS lgc n z
```

This is the real quotient-descent gate.  Once it is proved, the reduced function
can be defined on `BHW.ReducedPermutedExtendedTubeN d m` by choosing any absolute
PET representative `z` of the reduced point and evaluating
`bvt_selectedAbsolutePETGluedValue OS lgc (m + 1) z`; the theorem above gives
representative independence because equal reduced differences differ by a
uniform complex translation.

The proof should follow the already-existing base-fiber architecture, but with
the selected glued scalar in place of the old global `W_analytic_BHW` scalar:

```lean
theorem bvt_selectedAbsolutePETGluedValue_translationLocal
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.PermutedExtendedTube d n) :
    ∃ ε > 0, ∀ t : ℂ, ‖t‖ < ε →
      (fun k μ => z k μ + t * c μ) ∈ BHW.PermutedExtendedTube d n ∧
      bvt_selectedAbsolutePETGluedValue OS lgc n
          (fun k μ => z k μ + t * c μ) =
        bvt_selectedAbsolutePETGluedValue OS lgc n z
```

Local translation should be proved by unpacking a PET witness
`z = Λ • w` with `w ∈ PermutedForwardTube π`, shrinking `t` so the same
permuted forward-tube branch remains valid, and chaining:

```text
G(z + t c)
= G(Λ • (w + t Λ⁻¹c))       by selected Lorentz invariance
= G(w + t Λ⁻¹c)             by selected Lorentz invariance
= bvt_F((w + t Λ⁻¹c)∘π)     by selected PET branch equality + FT agreement
= bvt_F(w∘π)                by selected forward-tube translation invariance
= G(w)
= G(z)
```

The local proof requires one additional named selected forward-tube theorem:

```lean
theorem bvt_F_translation_invariant_forwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (c : Fin (d + 1) → ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ BHW.ForwardTube d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ BHW.ForwardTube d n) :
    bvt_F OS lgc n (fun k μ => z k μ + c μ) =
      bvt_F OS lgc n z
```

This should be a direct extraction from
`bvt_absoluteForwardTubeInput (d := d) OS lgc (n - 1)` when `n = m + 1`, plus
the existing `AbsoluteForwardTubeInput.translation_invariant` field.  The
`n = 0` case should be treated separately or avoided by stating the selected
quotient-descent theorem at public arity `m + 1`.

To globalize local translation to arbitrary `c`, define the selected base-fiber
value for fixed reduced tail:

```lean
def bvt_selectedBaseFiberValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc (m + 1))
    (ζtail : Fin m → Fin (d + 1) → ℂ) :
    (Fin (d + 1) → ℂ) → ℂ :=
  fun ζ₀ =>
    bvt_selectedAbsolutePETGluedValue OS lgc (m + 1)
      (baseFiberConfig m d ζtail ζ₀)
```

Then prove:

```lean
theorem fderiv_bvt_selectedBaseFiberValue_eq_zero
theorem exists_isConst_bvt_selectedBaseFiberValue_of_isPreconnected
theorem bvt_selectedAbsolutePETGluedValue_translationInvariant_of_baseFiber_isPreconnected
```

The remaining mathematical gap is therefore sharply isolated: either prove the
needed `IsPreconnected (baseFiber m d ζtail)` geometry without relying on the
old WIP `sorry`, or give a different direct proof of selected
translation-fiber constancy.  Until that geometry is closed, the reduced
quotient descent is **not** 100% implementation-ready.

Once PET value-invariance exists, define the selected translated-PET value
without any arbitrary branch choice.  The purely geometric part of this step is
now implemented in `ForwardTubeLorentz.lean`: for any scalar `F` on PET that is
invariant under uniform complex translations between PET points,
`translatedPETValue F z hz` evaluates `F` at a chosen PET witness for
`z ∈ TranslatedPET`, and theorems
`translatedPET_value_eq_of_translation_invariant`,
`translatedPETValue_eq_on_PET`, and
`translatedPETValue_translation_invariant` prove witness independence,
agreement on PET, and TPET translation invariance.  The remaining theorem-2
task is therefore not the TPET choice algebra; it is to construct the selected
OS PET scalar `bvt_F_PETExtension` with the required PET translation
invariance, non-circularly.

```lean
theorem isOpen_translatedPET {d n : ℕ} [NeZero d] :
    IsOpen (TranslatedPET d n) := by
  -- `TranslatedPET` is the union over uniform translations `c` of the
  -- preimages of the open `PermutedExtendedTube d n` under
  -- `z ↦ fun k μ => z k μ + c μ`.

theorem translatedPET_perm {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ TranslatedPET d n) :
    (fun k => z (σ k)) ∈ TranslatedPET d n := by
  -- If `z + c` is in the PET, then `(z ∘ σ) + c` is in the PET by absorbing
  -- the extra permutation into the PET permutation index.

theorem translatedPET_perm_iff {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    (fun k => z (σ k)) ∈ TranslatedPET d n ↔ z ∈ TranslatedPET d n := by
  -- Apply `translatedPET_perm` with `σ` and with `σ.symm`.

theorem bvt_F_PETExtension_value_on_translatedPET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c₁ c₂ : Fin (d + 1) → ℂ)
    (h₁ : (fun k μ => z k μ + c₁ μ) ∈ PermutedExtendedTube d n)
    (h₂ : (fun k μ => z k μ + c₂ μ) ∈ PermutedExtendedTube d n) :
    bvt_F_PETExtension OS lgc n (fun k μ => z k μ + c₁ μ) =
      bvt_F_PETExtension OS lgc n (fun k μ => z k μ + c₂ μ) := by
  have key :=
    bvt_F_PETExtension_translation_invariant_on_PET
      (d := d) OS lgc n (fun μ => c₂ μ - c₁ μ)
      (fun k μ => z k μ + c₁ μ) h₁
      (by
        convert h₂ using 1
        ext k μ
        ring)
  simpa [sub_eq_add_neg, add_assoc] using key.symm

noncomputable def bvt_F_on_translatedPET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n) : ℂ :=
  translatedPETValue (bvt_F_PETExtension OS lgc n) z hz
```

Then mirror the existing translated-PET API:

```lean
theorem bvt_F_on_translatedPET_eq_on_PET
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz_pet : z ∈ PermutedExtendedTube d n)
    (hz_tpet : z ∈ TranslatedPET d n) :
    bvt_F_on_translatedPET OS lgc n z hz_tpet =
      bvt_F_PETExtension OS lgc n z

theorem bvt_F_on_translatedPET_translation_invariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (c : Fin (d + 1) → ℂ)
    (hz : z ∈ TranslatedPET d n)
    (hzc : (fun k μ => z k μ + c μ) ∈ TranslatedPET d n) :
    bvt_F_on_translatedPET OS lgc n z hz =
      bvt_F_on_translatedPET OS lgc n (fun k μ => z k μ + c μ) hzc
```

If an everywhere-defined integrand is later needed, it may follow the existing
`F_ext_on_translatedPET_total` pattern:

```lean
noncomputable def bvt_F_on_translatedPET_total ... z :=
  if hz : z ∈ TranslatedPET d n then
    bvt_F_on_translatedPET OS lgc n z hz
  else 0
```

but this total version is only honest when paired with the null-set theorem
`ae_euclidean_points_in_translatedPET` or a support hypothesis proving the
integrand is used only on `TranslatedPET`.  It must not be used as a pointwise
extension off `TranslatedPET`.

Only after this selected translated-PET package is available should the
translated positive-time compact-support argument continue.  In that version,
positive-time translation is used to place Wick-rotated Euclidean points in a
forward/PET witness, while the final comparison back to the original support is
performed by `bvt_F_on_translatedPET_translation_invariant`, not by a false
Jost/ET membership-transport theorem.

The following raw `extendF` theorem remains an ET-local pointwise sublemma.  It
is useful on real-open neighborhoods where both the original and permuted real
configurations are already in PET/ET.  It is **not** by itself the translated
compact-support theorem, because positive-time translation does not transport
Jost/ET membership:

```lean
theorem bvt_F_extendF_perm_pointwise_of_positive_distinct
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (x : NPointDomain d n)
    (hxV : x ∈ V)
    (hpos : ∀ k : Fin n, 0 < x k 0)
    (hdistinct : ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0) :
    BHW.extendF (bvt_F OS lgc n)
        (BHW.realEmbed (fun k => x (σ k))) =
      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)
```

Proof sketch for the pointwise theorem:

1. Choose the sorted order `τ` of the positive, pairwise-distinct time
   coordinates of `x`.
3. Because the strict inequalities and positivity are open, choose a real-open
   neighborhood `Vx ⊆ V` on which the same `τ` keeps every point in
   `EuclideanOrderedPositiveTimeSector τ`.
4. Apply the sector-local branch-envelope theorem on `Vx`.
5. Apply `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` on
   `Vx`, using the OS Euclidean compact-test equality transported by
   `bvt_F_perm`.
6. Specialize the resulting real-edge equality at `x`.

After the selected translated-PET repair and the corresponding TPET pointwise
positive-sector theorem are available, package the compact pairing theorem.
The theorem statement below is still the desired raw `extendF` compact pairing
on the original PET-controlled support, but its proof must pass through
translated-PET values during the positive-time translation step:

```lean
theorem bvt_F_distributionalEOW_permBranch_from_euclideanEdge_translatedSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n)
    (φ : SchwartzNPoint d n)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (σ k))) * φ x
      =
    ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- 1. Rewrite the raw `extendF` values on the original support as
  --    `bvt_F_on_translatedPET`, using `bvt_F_on_translatedPET_eq_on_PET`
  --    and the hypotheses `hV_ET`, `hV_permET`.
  -- 2. Choose a uniform `A` from compactness of `tsupport φ`.
  -- 3. Change variables by `positiveTimeTranslate A`, using the checked
  --    `timeShiftSchwartzNPoint` support lemmas.
  -- 4. Use `bvt_F_on_translatedPET_translation_invariant` to move the TPET
  --    values between the original and translated real configurations.
  -- 5. Apply the positive-time, pairwise-distinct TPET pointwise theorem a.e.
  --    on the translated support.
  -- 6. Remove time-tie walls with `ae_pairwise_distinct_timeCoords` and finish
  --    by `integral_congr_ae`.
```

This route avoids non-Schwartz indicators entirely.  Time-tie walls are removed
only by `integral_congr_ae` using the finite-union null theorem.  Sector choices
are made locally around each a.e. point, not by multiplying the test by sector
indicator functions.

The currently missing theorem before this compact package is implementation-ready
is the TPET pointwise positive-sector version:

```lean
theorem bvt_F_on_translatedPET_perm_pointwise_of_positive_distinct
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n)
    (hpairwiseJost :
      ∀ i j : Fin n, i ≠ j →
        MinkowskiSpace.IsSpacelike d (fun μ => x i μ - x j μ))
    (hpos : ∀ k : Fin n, 0 < x k 0)
    (hdistinct : ∀ i j : Fin n, i ≠ j → x i 0 ≠ x j 0)
    (hx_tpet : BHW.realEmbed x ∈ TranslatedPET d n)
    (hxσ_tpet : BHW.realEmbed (fun k => x (σ k)) ∈ TranslatedPET d n) :
    bvt_F_on_translatedPET OS lgc n
        (BHW.realEmbed (fun k => x (σ k))) hxσ_tpet =
      bvt_F_on_translatedPET OS lgc n (BHW.realEmbed x) hx_tpet
```

This statement uses the translation-invariant, pairwise-difference Jost
condition, not the absolute `BHW.JostSet`, because the latter is not preserved
by uniform time translation.  Its proof is the sector-local branch-envelope
argument: choose the sorted positive sector, use the Wick-section identity on a
small real-open neighborhood, and identify the resulting branch values with the
selected translated-PET values via the witness supplied by
`bvt_F_on_translatedPET`.

The older finite-sector export can remain as a fallback theorem slot, but it
should be secondary to the translated-compact-support theorem above:

```lean
theorem bvt_F_distributionalEOW_permBranch_from_euclideanEdge_sectorDecomp
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_open : IsOpen V)
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (hV_ET : ∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hV_permET :
      ∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) :
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (σ k))) * φ x
        =
      ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
  -- Fallback route only: split the translated compact pairing into finitely
  -- many ordered positive-time sectors plus the time-tie/null-boundary pieces.
  -- On each sector, apply the sector-local branch envelope and the local
  -- Wick-section identity theorem.  The tie walls require a null-set /
  -- integrable-zero lemma or a smooth sector partition; do not use raw
  -- indicator functions as Schwartz tests.
```

With the sector-local envelope theorem, the sector-decomposition export, and
the local Wick-section identity theorem, the proof of
`bvt_F_distributionalEOW_permBranch_from_euclideanEdge` becomes mechanical:

1. If `V = ∅`, prove both sides are zero from
   `tsupport φ ⊆ ∅`.
2. Otherwise obtain `⟨U, F_id, F_perm, ...⟩` from the branch-envelope theorem.
3. Apply
   `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen` to
   `F_id` and `F_perm`, using `hEuclid` rewritten by the two Wick-edge
   equations from the envelope.
4. Specialize the resulting `Set.EqOn F_id F_perm U` at
   `BHW.realEmbed x` for each `x ∈ V`, and rewrite by the two real-edge
   equations from the envelope.
5. Convert that pointwise equality on `V` to the compact-test integral equality:
   outside `tsupport φ`, the factor `φ x` is zero; inside `tsupport φ`, use
   `hφ_tsupport : tsupport φ ⊆ V`.

This leaves no hidden raw-boundary continuity assumption.  The only continuity
used in the conversion from distributional equality to pointwise equality is
continuity of holomorphic functions on the interior domain `U`, exactly as in
the checked `OSToWightmanTubeIdentity` proof.

Equivalently, package this as `bvt_F_hasPermutationEdgeDistributionEquality`
as compact-test pairing equality.  Then the checked theorem
`BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality` converts this compact
edge pairing equality to pointwise equality on `V`.

The `bvt_W` theorem below is only a compatibility adapter after the direct
branch equality has been proved.  It is useful for comparing with the private
hLC proof, but it should not be treated as the hard theorem-2 core:

```lean
theorem bvt_W_perm_invariant_on_compactJostOverlap_from_OS
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ (σ : Equiv.Perm (Fin n))
      (V : Set (NPointDomain d n)),
      IsOpen V →
      (∀ x ∈ V, x ∈ BHW.JostSet d n) →
      (∀ x ∈ V, BHW.realEmbed x ∈ BHW.ExtendedTube d n) →
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (σ k)) ∈ BHW.ExtendedTube d n) →
    ∀ (φ : SchwartzNPoint d n),
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ V →
      bvt_W OS lgc n (BHW.permuteSchwartz (d := d) σ⁻¹ φ) =
      bvt_W OS lgc n φ := by
  -- Apply `bvt_F_extendF_perm_edgeDistribution_eq_from_OS`, change variables,
  -- and use boundary recovery to identify the two branch distributions with
  -- `bvt_W OS lgc n φ` and
  -- `bvt_W OS lgc n (BHW.permuteSchwartz σ⁻¹ φ)`.
```

Do not replace this by a simple adjacent-swap induction over a global
`tsupport ⊆ JostSet` theorem unless every intermediate permutation is supplied
with its transported real-open ET/permuted-ET overlap.  The local branch theorem
above is the exact compact-support hypothesis the public `SCV.eqOn_open...`
spine needs.

Its proof must be documented as the following concrete sublemmas:

```lean
def BHW.permuteZeroDiagonalSchwartz
    (σ : Equiv.Perm (Fin n)) (f : ZeroDiagonalSchwartz d n) :
    ZeroDiagonalSchwartz d n := ...

@[simp] theorem BHW.permuteZeroDiagonalSchwartz_apply
    (σ : Equiv.Perm (Fin n)) (f : ZeroDiagonalSchwartz d n)
    (x : NPointDomain d n) :
    (BHW.permuteZeroDiagonalSchwartz (d := d) σ f).1 x =
      f.1 (fun k => x (σ k))

theorem BHW.jostSet_disjoint_coincidenceLocus :
    Disjoint (BHW.JostSet d n) (CoincidenceLocus d n)

theorem zeroDiagonal_of_tsupport_subset_jostOverlap
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    VanishesToInfiniteOrderOnCoincidence φ

theorem bvt_F_euclidean_perm_branch_pairing_eq_from_E3
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (V : Set (NPointDomain d n))
    (hV_jost : ∀ x ∈ V, x ∈ BHW.JostSet d n)
    (φ : SchwartzNPoint d n)
    (hφ_tsupport : tsupport (φ : NPointDomain d n → ℂ) ⊆ V) :
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x (σ k))) * φ x
      =
    ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * φ x

theorem bvt_F_acrOne_perm_branches_have_common_euclidean_edge
    ... :
    -- package the previous equality as equality of the two ACR(1) branch
    -- boundary distributions on the Euclidean edge.

theorem bvt_F_perm_branch_distribution_eq_on_jostOverlap_from_OS
    ... :
    -- many-variable EOW / totally-real identity transfers the common Euclidean
    -- edge distribution to the real-open Jost overlap `V`.

theorem bvt_W_perm_eq_of_branch_distribution_eq_on_jostOverlap
    ... :
    -- use `tendsto_extendF_boundary_integral_of_hasCompactSupport_ET` and
    -- `bvt_boundary_values` for `φ` and `BHW.permuteSchwartz σ⁻¹ φ`.
```

The proof transcript for the branch theorem should then be:

1. Set `F := bvt_F OS lgc n`.
2. From `hφ_tsupport : tsupport φ ⊆ V`, obtain
   `hφ_zero : VanishesToInfiniteOrderOnCoincidence φ` using
   `BHW.jostSet_disjoint_coincidenceLocus`.
3. Form the honest Euclidean test
   `φZ : ZeroDiagonalSchwartz d n := ⟨φ, hφ_zero⟩`.
4. Use `OS.E3_symmetric` on `φZ` and
   `BHW.permuteZeroDiagonalSchwartz σ⁻¹ φZ`; rewrite both sides with
   `bvt_euclidean_restriction`; use `BHW.integral_perm_eq_self` to obtain the
   Euclidean branch pairing equality

   ```lean
   ∫ x, F (fun k => wickRotatePoint (x (σ k))) * φ x =
   ∫ x, F (fun k => wickRotatePoint (x k)) * φ x
   ```

   The inverse permutation in `permuteZeroDiagonalSchwartz σ⁻¹` is deliberate:
   after the change of variables, it produces the branch
   `x ↦ F (wickRotatePoint (x ∘ σ))`, matching the left trace
   `extendF F (realEmbed (x ∘ σ))`.

5. Feed that equality, the selected `bvt_F_acrOne_package`, and the
   many-variable EOW/totally-real identity theorem into the branch theorem

   ```lean
   theorem bvt_F_extendF_perm_edgeDistribution_eq_from_OS
       ... :
       ∫ x : NPointDomain d n,
           BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
         =
       ∫ x : NPointDomain d n,
           BHW.extendF F (BHW.realEmbed x) * φ x
   ```

This directly supplies the `hEdge` input for
`BHW.extendF_perm_eq_on_realOpen_of_edgePairingEquality`.  No difference-form
rewrite is needed in the uniqueness adapter.

#### Consumer audit: arbitrary transposition is the live surface

The current public theorem-2 bridge does not ask only for adjacent swaps.  In
`OSToWightmanBoundaryValues.lean`, `bvt_locally_commutative` calls

```lean
theorem bv_local_commutativity_transfer_of_swap_pairing
```

with the private frontier

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) *
                Complex.I) * g x
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) *
                Complex.I) * f x
```

The swap is an arbitrary transposition `Equiv.swap i j`.  Therefore the
checked adjacent-overlap theorem

```lean
bvt_F_extendF_adjacent_overlap_of_selectedEdgeData
```

cannot by itself close the current consumer.  The old bubble-sort idea of
decomposing `swap i j` into adjacent swaps fails at the real-edge level because
the support hypothesis only says the selected pair `(x i, x j)` is spacelike;
it does not say the intermediate adjacent pairs are spacelike.  This is why a
naive adjacent-swap induction is not an OS proof.

The next proof-doc stage must choose between two precise consumer shapes:

1. **Rewrite the downstream bridge to an adjacent-only locality surface.**
   This would replace or supplement `bv_local_commutativity_transfer_of_swap_pairing`
   with a theorem that only asks for adjacent `swap i (i+1)` at the BV pairing
   level, and then prove the public `IsLocallyCommutativeWeak` arbitrary
   transposition statement by a separate distributional/permutation argument.
   This is only valid if that second step does not reintroduce the same
   unsupported intermediate-spacelike assumptions.

2. **Keep the arbitrary-transposition consumer and supply PET transport.**
   This is closer to the classical BHW route: use real-edge equality only for
   the selected spacelike pair, and use analytic continuation in ET/PET to
   transport through intermediate non-spacelike reorderings.  In this shape,
   adjacent edge data remains the local seed, but a PET-level transport or
   single-valuedness theorem is still needed to reach arbitrary `swap i j`.

Thus the immediate next blocker is not yet the generic
`BHW.petGermChainReady_exists`; it is the smaller decision theorem:

```lean
-- schematic
theorem theorem2_arbitrarySwap_consumer_reduction_decision :
  -- Either produce an adjacent-only replacement for
  -- `bv_local_commutativity_transfer_of_swap_pairing`,
  -- or show the current arbitrary-swap bridge requires PET-level
  -- all-branch transport.
```

For proof documentation, this means the next transcript must expand the
arbitrary-swap pairing proof at the canonical shell:

1. rewrite the left integral with `g x = f (x ∘ swap i j)`;
2. change variables so both integrals are tested against `f`;
3. identify the two complex shell configurations related by `swap i j`;
4. determine exactly which PET sectors contain those two shells under the
   selected spacelike support hypothesis;
5. show whether the equality follows from one adjacent overlap theorem or from
   a necessary PET transport through additional sector branches.

Only after this transcript is written should we decide whether to implement a
global PET monodromy theorem or a narrower arbitrary-swap canonical-shell
transport theorem.

The optional `bvt_W` compatibility adapter then continues:

6. Set `φσ := BHW.permuteSchwartz σ⁻¹ φ` and use the change-of-variables
   identity already present in the private proof:

   ```lean
   ∫ x, BHW.extendF F (BHW.realEmbed x) * φσ x =
   ∫ x, BHW.extendF F (BHW.realEmbed (fun k => x (σ k))) * φ x
   ```

7. Recover both Wightman boundary values with
   `tendsto_extendF_boundary_integral_of_hasCompactSupport_ET` and
   `bvt_boundary_values`.  The ET support for `φ` is `hV_ET`; the ET support
   for `φσ` is transported from `hV_permET`.
8. Conclude

   ```lean
   bvt_W OS lgc n φσ = bvt_W OS lgc n φ
   ```

   This is a useful consistency theorem, but it is no longer the preferred
   input for the pointwise real-open proof.

This is the precise place where the OS-II correction matters: the proof must use
the repaired many-variable `bvt_F` / ACR(1) branch package.  It must not invoke a
one-variable Lemma-8.8-style continuation or a hidden global locality theorem.

This subpacket is now the primary proof-doc gap.  It is smaller and more
OS-faithful than the finite-height endpoint-symmetry problem, but it is still
not a one-line instantiation of any checked production theorem.  The exact
missing proof is the OS-side branch-distribution equality
`bvt_F_extendF_perm_edgeDistribution_eq_from_OS`, packaged afterward as
`bvt_F_hasPermutationEdgeDistributionEquality`, plus the public exposure of the
already-present `extendF`-overlap/PET-extension spine.

Then the public theorem can avoid the overstrong private finite-shell frontier:

```lean
theorem bvt_locally_commutative_from_symmetric_PET_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  -- obtain `Fext` from `bvt_F_symmetric_PET_extension`;
  -- apply `bv_local_commutativity_transfer_of_symmetric_PET_boundary`
  -- with `F := bvt_F OS lgc n` and `W_n := bvt_W OS lgc n`.
```

If we deliberately keep the current finite-height consumer
`bv_local_commutativity_transfer_of_swap_pairing`, then the stronger theorem
`bvt_F_swapCanonical_pairing` still requires the symmetric-envelope or verified
slice-reflection packet below.  But that packet should now be treated as the
price of retaining an overstrong sufficient condition, not as the only OS-route
path to theorem 2.

The slice reduction remains a candidate way to prove the stronger
`exists_reduced_canonicalRealSwap_symmetricEnvelope`, but it is not currently
an implementation-ready route.  It becomes valid only after endpoint-hit lemmas
show that the slice really reaches the two finite shell points above and
produces the reflection/symmetry map `R`.  The candidate packet is:

```lean
def selectedPairTimeSlice
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) :
    ℂ → ReducedNPointConfig d m :=
  -- vary only the complex relative-time normal to the selected pair, keeping
  -- the reduced spatial data and all spectator reduced coordinates fixed.
  -- The exact Lean definition should be written using
  -- `(realDiffCoordCLE (m + 1) d).symm (prependBasepointReal d m x₀ ξ)` so the
  -- pair coordinates are changed in absolute coordinates and then pushed back
  -- through `reducedDiffMap`.

theorem selectedPairTimeSlice_real_interval_spacelike
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t| < δ →
        selectedPairTimeSlice (d := d) m i j ξ (t : ℂ) ∈
          reducedSpacelikeSwapEdge (d := d) m i j := by
  -- openness of the spacelike cone around the selected pair difference.

theorem selectedPairTimeSlice_upper_mem_reducedForwardTube
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) (hε : 0 < ε) :
    selectedPairTimeSlice (d := d) m i j ξ (Complex.I * ε) ∈
      BHW.ReducedForwardTubeN d m := by
  -- canonical ordering gives positive imaginary relative time in the selected
  -- normal direction, with spectator imaginary differences fixed in the
  -- canonical product cone.

theorem selectedPairTimeSlice_lower_mem_swapPulledForwardTube
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) (hε : 0 < ε) :
    selectedPairTimeSlice (d := d) m i j ξ (-Complex.I * ε) ∈
      {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
        BHW.ReducedForwardTubeN d m} := by
  -- swapped ordering gives the opposite imaginary normal for the selected pair.

theorem selectedPairTimeSlice_boundary_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t| < δ →
        bvt_F_reduced (d := d) OS lgc m
          (selectedPairTimeSlice (d := d) m i j ξ (t : ℂ))
        =
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
            (selectedPairTimeSlice (d := d) m i j ξ (t : ℂ))) := by
  -- combine `selectedPairTimeSlice_real_interval_spacelike` with
  -- `bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge`.

theorem selectedPairTimeSlice_hits_canonicalReducedShell
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) :
    selectedPairTimeSlice (d := d) m i j ξ (Complex.I * ε) =
      canonicalReducedShell (d := d) m ξ ε := by
  -- Required endpoint lemma.  If this equality is false for the chosen slice,
  -- the slice route is not the right bridge.

theorem selectedPairTimeSlice_hits_realPermutedCanonicalReducedShell
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (ε : ℝ) :
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
      (selectedPairTimeSlice (d := d) m i j ξ (-Complex.I * ε))
    =
      realPermutedCanonicalReducedShell (d := d) m i j ξ ε := by
  -- Required endpoint lemma.  This is the missing check that the lower branch
  -- endpoint is the real-permuted canonical shell, not just some swapped
  -- one-variable normal perturbation.

theorem selectedPairTimeSlice_connected_domain_to_all_heights
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Ω : Set ℂ,
      IsOpen Ω ∧ IsPreconnected Ω ∧
      Complex.I * ε ∈ Ω ∧ -Complex.I * ε ∈ Ω ∧
      (∀ τ ∈ Ω, selectedPairTimeSlice (d := d) m i j ξ τ ∈
        (BHW.ReducedForwardTubeN d m) ∪
        {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
          BHW.ReducedForwardTubeN d m} ∪
        {ζ | ∃ ξ₀ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
          ζ = fun k μ => (ξ₀ k μ : ℂ)}) := by
  -- Required propagation lemma.  Local 1D EOW near the real interval is not
  -- enough unless the continuation domain connects the local wedge to the
  -- requested finite height `ε`.

theorem selectedPairTimeSlice_reflection_symmetry
    (Ω : Set ℂ) (H : ℂ → ℂ) (r : ℂ → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    IsOpen Ω →
    IsConnected Ω →
    DifferentiableOn ℂ H Ω →
    DifferentiableOn ℂ r Ω →
    (∀ z ∈ Ω, r z ∈ Ω) →
    Complex.I * ε ∈ Ω →
    r (Complex.I * ε) = -Complex.I * ε →
    (∃ a b : ℝ, a < b ∧
      Set.Ioo a b ⊆ {t : ℝ | (t : ℂ) ∈ Ω} ∧
      (∀ t : ℝ, t ∈ Set.Ioo a b → H (r (t : ℂ)) = H (t : ℂ))) →
    H (-Complex.I * ε) = H (Complex.I * ε) := by
  -- This is the slice analogue of the reduced envelope symmetry map `R`.
  -- Connectedness of the slice domain alone is not enough: a holomorphic
  -- function is not constant on connected domains.  The proof is a
  -- one-dimensional totally-real identity theorem applied to
  -- `fun τ => H (r τ) - H τ`, followed by evaluation at `Complex.I * ε`.

theorem reduced_local_EOW_canonicalRealSwap_from_verified_slice
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hsp : MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ))
    (ε : ℝ) (hε : 0 < ε) :
    bvt_F_reduced (d := d) OS lgc m
      (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (selectedPairTimeSlice (d := d) m i j ξ (-Complex.I * ε)))
    =
    bvt_F_reduced (d := d) OS lgc m
      (selectedPairTimeSlice (d := d) m i j ξ (Complex.I * ε)) := by
  -- Define one-variable functions
  -- `f_plus τ := bvt_F_reduced ... (selectedPairTimeSlice ... τ)`
  -- on the upper half-plane and
  -- `f_minus τ := bvt_F_reduced ... (permOnReducedDiff swap
  --   (selectedPairTimeSlice ... τ))`
  -- on the lower half-plane.
  -- Apply `edge_of_the_wedge_1d` on the real interval from
  -- `selectedPairTimeSlice_boundary_eq`.
  -- Then prove the reflected slice identity, not mere connectedness, on the
  -- connected upper/lower continuation domain.  Use
  -- `selectedPairTimeSlice_reflection_symmetry` to compare the values at the
  -- two endpoint parameters.
  -- Finally rewrite the two endpoints using
  -- `selectedPairTimeSlice_hits_canonicalReducedShell` and
  -- `selectedPairTimeSlice_hits_realPermutedCanonicalReducedShell`.
```

This candidate slice packet is useful only if the endpoint, connectedness, and
reflection-symmetry lemmas above are true.  Until then, the implementation-ready
statement remains the broader symmetric-envelope seam
`exists_reduced_canonicalRealSwap_symmetricEnvelope`, followed by
`reduced_connectedEnvelope_symmetry_transport`.  In particular, theorem 2 as a
whole is not 100% Lean-ready yet, although the reduced algebraic packet
preceding this analytic seam is ready for implementation.

Then the absolute pointwise theorem is only an adapter:

1. set `m := n - 1` after eliminating the vacuous `n = 0` case;
2. factor both absolute shell values through `bvt_F_reduced`;
3. rewrite their reduced imaginary directions using the two direction lemmas;
4. rewrite the support hypothesis with `reducedPairDiff_reducedDiffMapReal`;
5. apply
   `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`.

## 7. Exact proof decomposition for theorem 2

After the candidate-symmetry audit, the recommended Lean proof should follow
the OS-I-faithful boundary route first.

1. Publicize the non-circular `extendF` overlap/PET-extension spine currently
   present only as private support in `PermutationFlow.lean`.
2. Prove `bvt_F_hasPermutationEdgeDistributionEquality`, the OS-side real-open
   Jost edge distribution equality replacing the hLC input in the current BHW
   theorem.
3. Use that edge equality to prove `bvt_F_extendF_perm_overlap`, i.e. the
   `extendF` equality on every ET/permuted-ET overlap needed by
   `bargmann_hall_wightman_theorem_of_extendF_perm`.
4. Prove or expose the OS-side PET extension theorem
   `bvt_F_symmetric_PET_extension`.
5. Prove the generic Jost/BHW boundary transfer theorem
   `bv_local_commutativity_transfer_of_symmetric_PET_boundary`.
6. Replace the proof of `bvt_locally_commutative` so it calls the boundary
   transfer theorem directly, using `bvt_F`, `bvt_W`, `bvt_boundary_values`,
   and the PET extension from step 4.
7. Leave `bvt_F_swapCanonical_pairing` as a private overstrong sufficient
   theorem, or retire it from the active dependency path if no other consumer
   needs finite-height shell equality.

This route keeps the proof aligned with OS I Section 4.5: locality is a
statement about boundary distributions of a symmetric BHW continuation, not
about equality of every positive-height canonical shell integral.

If we decide to retain the current finite-height consumer anyway, then the
fallback proof order is:

1. Prove the algebraic reduced-shell packet:
   `bvt_F_reduced`, `bvt_F_eq_bvt_F_reduced_reducedDiffMap`, the canonical
   direction lemmas, `reducedPairDiff_reducedDiffMapReal`,
   `bvt_F_reduced_permOnReducedDiff`, and
   `permOnReducedDiff_swap_permutedCanonicalDirection`.
2. Prove the reduced permutation adapter
   `bvt_F_reduced_permutedDirection_to_realPermutedCanonical`.
3. Prove the reduced local-edge theorem
   `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike`.
   This factors through `reducedSpacelikeSwapEdge`,
   `bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge`, branch
   holomorphicity, and `reduced_local_EOW_canonicalRealSwap`.
4. Derive
   `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`
   as a short adapter from the previous two steps.
5. Use the reduced packet to prove
   `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike`.
6. Use `bvt_F_perm` to prove
   `bvt_F_swapCanonical_pointwise_of_spacelike`.
7. Use measure-preserving coordinate swap and support-zero outside `tsupport f`
   to prove `bvt_F_swapCanonical_pairing_from_transposition_pointwise`.
8. Feed the result into
   `bv_local_commutativity_transfer_of_swap_pairing`.

The fallback should not be started until the symmetric-envelope or verified
slice-reflection packet is implementation-ready.  The theorem should not be
attacked by opening a new permutation-continuation front in the middle of
`OSToWightmanBoundaryValues.lean`; the generic PET/Jost machinery belongs in
the BHW/SCV layer.

## 8. Historical docs that are no longer frontier guidance

The following docs are historical and should not be used as primary route
guidance for theorem 2:

1. `docs/edge_of_the_wedge_proof_plan.md`
2. `docs/edge_of_the_wedge_gap_analysis.md`

Both were written before the theorem

```lean
SCV.edge_of_the_wedge_theorem
```

was proved. They are still useful for mathematical context, but they do not
describe the current production frontier on `main`.

## 9. Exact theorem-name dictionary for theorem 2

The later proof should distinguish checked-present support surfaces from the
new theorem-2 closure slots.

Checked-present surfaces to use only where their hypotheses are non-circular:

1. `bvt_F_perm`
2. `bv_local_commutativity_transfer_of_swap_pairing`
3. `exists_real_open_nhds_adjSwap`
4. `boundary_function_continuous_forwardTube_of_flatRegular`
5. `edge_of_the_wedge`
6. `SCV.edge_of_the_wedge_theorem`
7. `eqOn_openConnected_of_distributional_wickSection_eq_on_realOpen`
8. `bvt_F_acrOne_package`

Checked-present surfaces that are comparison/supplier context but are not
direct final theorem-2 calls on `W := bvt_W OS lgc`:

1. `W_analytic_swap_boundary_pairing_eq`
2. `analytic_extended_local_commutativity`
3. `analytic_boundary_local_commutativity_of_boundary_continuous`
4. `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`

Primary planned theorem-2 closure slots:

Priority boundary after the #1065 audit and the OS I §4.5 reread: slots 1-13
are active only as the local Lean bridge into the paper's symmetric
continuation stage.  The paper-level target starts at slot 25: construct the
symmetric PET/BHW continuation and then apply the Jost boundary theorem to
locality.  Slots 18-24 are deferred BHW/PET single-valuedness work; they should
not receive additional implementation or proof-doc expansion until
`bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le` has a complete
Lean-ready transcript for the `2 ≤ d` branch.  The `d = 1` closure is a
separate branch: either prove a dedicated dimension-one real-open edge theorem
with the same `SelectedAdjacentPermutationEdgeData` fields, or prove a direct
dimension-one complex-edge boundary-locality theorem.  Do not describe a
complex-edge-only theorem as if it filled the real-open
`SelectedAdjacentPermutationEdgeData.edge_witness` field.

1. `bvt_F_restrictedLorentzInvariant_forwardTube`
2. `bvt_F_complexLorentzInvariant_forwardTube`
3. `choose_os45_real_open_edge_for_adjacent_swap`
4. `zeroDiagonal_of_tsupport_subset_jostOverlap`
5. `bvt_F_euclidean_adjacent_branch_pairing_eq_from_E3`
6. `SCV.edge_of_the_wedge_theorem_connected_of_connected_edge`
7. Corrected OS §4.5 branch-difference supplier, not yet implementation-ready:
   replace the retracted
   `BHW.localAdjacentOS45OppositeWedgeChart_at_jostSeed` / full-tube
   `pos_orbit_*` route by either a generic BHW/PET branch theorem plus Jost
   boundary-value transfer, or a genuinely local EOW chart over a real edge `E`
   with no point-permutation-as-Lorentz claim.
8. Corrected preliminary adjacent geometry after slot 7 is rewritten.  The
   proved `BHW.permAct_*` helpers and
   `BHW.os45_adjacent_orderedWickSeeds_mem_forwardTube` may be reused, but no
   replacement theorem may quantify full-dimensionally over a tube and require
   Lorentz orbit witnesses for point permutations.
9. Corrected branchwise boundary-value theorem for the OS §4.5
   branch-difference.  It must compare adjacent branch differences through the
   common analytic continuation / Jost boundary theorem, not through
   one-branch Wick-to-real equality and not through `extendF_preimage_eq`
   supplied by false orbit witnesses.
10. `os45_adjacent_branchDifferenceEnvelope_and_edge_exists_singleChart` only
   after slots 7-9 are rewritten; otherwise use
   `SCV.differenceEnvelope_of_localBoundaryCharts` as a local-chart gluing tool
   for the corrected local theorem shape.
11. `AdjacentOSEOWDifferenceEnvelope`
12. `bvt_F_adjacent_edgeWitness_from_OS_ACR_of_two_le`
13. `bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le`
    for the `2 ≤ d` real-edge branch only
14. `bvt_F_selectedAdjacentPermutationEdgeData_from_OS_d1` only if a
    dedicated non-circular `d = 1` real-open edge theorem is actually proved
15. `bvt_locally_commutative_boundary_route_of_one` if the `d = 1` proof uses
    a complex-edge/direct-boundary route instead of the real-open edge record
16. `SelectedAdjacentPermutationEdgeData`
17. `bvt_F_extendF_adjacent_overlap_of_selectedEdgeData`
18. `bvt_selectedPETBranch`
19. `bvt_selectedPETBranch_holomorphicOn_sector`
20. `bvt_selectedPETBranch_adjacent_eq_on_sector_overlap`
21. `BHW.PETGermChain`
22. `BHW.PETGermChainReady`
23. `BHW.pet_branch_independence_of_germChain`
24. `BHW.petGermChainReady_exists`
25. `BHW.extendF_pet_branch_independence_of_adjacent`
26. `bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData`
27. `BHW.F_permutation_invariance_of_petBranchIndependence` (implemented)
28. `BHW.fullExtendF_well_defined_of_petBranchIndependence` (implemented)
29. `BHW.bargmann_hall_wightman_theorem_of_adjacentBranchEquality`
30. `bvt_F_symmetric_PET_extension_of_adjacentEdgeData`
31. `BHW.permuteSchwartz`
32. `BHW.permute_support_jost`
33. `BHW.permute_tsupport_jost`
34. `BHW.permuteSchwartz_hasCompactSupport`
35. `BHW.integral_perm_eq_self`
36. `bvt_W_perm_invariant_on_compactJostOverlap_from_OS`
37. `bv_local_commutativity_transfer_of_symmetric_PET_boundary`
38. `bvt_locally_commutative_from_symmetric_PET_boundary`

The following older slot names are no longer primary construction targets:

1. `BHW.jostWitness_exists_for_perm_overlap`;
2. `BHW.isConnected_permForwardOverlapSet_for_perm`;
3. `bvt_F_extendF_perm_edgeDistribution_eq_from_OS`;
4. `bvt_F_hasPermutationEdgeDistributionEquality`;
5. `bvt_F_extendF_perm_overlap`;
6. `BHW.petSectorFiber_adjacent_connected`;
7. `BHW.extendF_pet_branch_independence_of_adjacent_of_sectorFiberConnected`;
8. `BHW.orbit_chamber_path_discretization`.

They may remain as conditional compatibility lemmas if their hypotheses are
explicitly supplied, but theorem 2 must not try to construct arbitrary
all-permutation real edge witnesses.  General permutation behavior must be
exported through adjacent edge data plus the PET monodromy / single-valuedness
theorem.

Do not insert `bvt_F_hasFlatRegularRepr` or
`bvt_F_boundary_continuous_at_real_support` into the primary list.  Those names
would require raw real-trace regularity of the Wightman boundary value and are
too strong for the theorem-2 OS route unless replaced by a sharply restricted
support theorem.  The primary bridge is the `extendF` equality on real Jost
edge points, not continuity of `bvt_F` on all real boundary points.

Fallback finite-height closure slots, needed only if the current overstrong
`bvt_F_swapCanonical_pairing` consumer is retained:

1. `choose_real_open_edge_for_adjacent_swap`
2. `swapped_support_lies_in_swapped_open_edge`
3. `bvt_F_hasFlatRegularRepr`
4. `bvt_F_boundary_continuous_at_real_support`
5. `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
6. `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
7. `canonical_adjacentSwap_shell_mem_EOW_domain`
8. `bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike`
9. `bvt_F_adjacentSwapCanonical_pointwise_of_spacelike`
10. `bvt_F_adjacentSwapCanonical_pairing_from_pointwise`
11. `bvt_F_reduced`
12. `bvt_F_eq_bvt_F_reduced_reducedDiffMap`
13. `canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC`
14. `permutedCanonicalForwardDirection_reducedDiff_eq`
15. `reducedDiffMap_canonicalShell_eq`
16. `reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq`
17. `reducedPairDiff_reducedDiffMapReal`
18. `bvt_F_reduced_permOnReducedDiff`
19. `permOnReducedDiff_swap_permutedCanonicalDirection`
20. `bvt_F_reduced_permutedDirection_to_realPermutedCanonical`
21. `reducedSpacelikeSwapEdge`
22. `isOpen_reducedSpacelikeSwapEdge`
23. `bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge`
24. `bvt_F_reduced_holomorphicOn_reducedForwardTube`
25. `bvt_F_reduced_holomorphicOn_swapPulledForwardTube`
26. `reduced_local_EOW_canonicalRealSwap`
27. `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike`
28. `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`
29. `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike`
30. `bvt_F_swapCanonical_pointwise_of_spacelike`
31. `bvt_F_swapCanonical_pairing_from_transposition_pointwise`

If a later proof jumps from checked BHW support context directly to
`bvt_F_swapCanonical_pairing` without either the primary boundary-level
PET/Jost route or the full fallback finite-shell packet above, the
implementation is drifting back toward a stale or circular locality plan.

## 10. Do not do this

1. Do not reintroduce edge-of-the-wedge as an axiom or a missing theorem.
2. Do not mix theorem 2 with theorem 3 positivity reductions.
3. Do not claim locality directly from permutation invariance of `bvt_F` alone;
   the real issue is boundary pairing and ET/Jost support geometry.
4. Do not use the historical edge-of-the-wedge gap notes as if they still
   described `main`.
5. Do not hide the finite canonical-shell interchange theorem inside the closing
   `sorry` if the overstrong finite-height consumer is retained.
6. Do not instantiate a checked BHW theorem with
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)` while proving theorem 2.
7. Do not use boundary-value recovery as if it proved finite-`ε` canonical
   shell equality.
8. Do not force the OS I locality proof through finite-shell equality if the
   boundary-level PET/Jost transfer theorem is available.

## 11. Minimal Lean pseudocode for the full closure

Primary PET-extension construction in the real-edge range `2 ≤ d`:

```lean
theorem bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SelectedAdjacentPermutationEdgeData OS lgc n := by
  -- Construct only adjacent-swap edge data:
  --   * adjacent overlap connectedness;
  --   * adjacent real-open edge witness;
  --   * compact-test edge equality from OS Euclidean symmetry and
  --     distributional EOW.
  -- Do not construct arbitrary all-permutation real edge witnesses.

theorem bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n)
    (π ρ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hzπ : z ∈ BHW.permutedExtendedTubeSector d n π)
    (hzρ : z ∈ BHW.permutedExtendedTubeSector d n ρ) :
    bvt_selectedPETBranch OS lgc n π z =
      bvt_selectedPETBranch OS lgc n ρ z := by
  exact
    BHW.extendF_pet_branch_independence_of_adjacent
      (d := d) n (bvt_F OS lgc n)
      (bvt_F_holomorphic (d := d) OS lgc n)
      (bvt_F_restrictedLorentzInvariant_forwardTube (d := d) OS lgc n)
      (by
        intro π i hi z hzπ hzπswap
        exact bvt_selectedPETBranch_adjacent_eq_on_sector_overlap
          (d := d) OS lgc n hEdge π i hi z hzπ hzπswap)
      π ρ z hzπ hzρ

theorem bvt_F_symmetric_PET_extension_of_adjacentEdgeData
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (hEdge : SelectedAdjacentPermutationEdgeData OS lgc n) :
    ∃ Fext : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Fext (BHW.PermutedExtendedTube d n) ∧
      (∀ z ∈ ForwardTube d n, Fext z = bvt_F OS lgc n z) ∧
      (∀ (Λ : ComplexLorentzGroup d) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (BHW.complexLorentzAction Λ z) = Fext z) ∧
      (∀ (σ : Equiv.Perm (Fin n)) z,
        z ∈ BHW.PermutedExtendedTube d n →
        Fext (fun k => z (σ k)) = Fext z) := by
  obtain ⟨Fext, hFext_holo, hFext_agree, hFext_lorentz, hFext_perm, _huniq⟩ :=
    BHW.bargmann_hall_wightman_theorem_of_adjacentBranchEquality
      (d := d) n (bvt_F OS lgc n)
      (bvt_F_holomorphic (d := d) OS lgc n)
      (bvt_F_restrictedLorentzInvariant_forwardTube (d := d) OS lgc n)
      (bvt_selectedPETBranch_allOverlap_eq_of_adjacentEdgeData
        (d := d) OS lgc n hEdge)
  exact ⟨Fext, hFext_holo, hFext_agree, hFext_lorentz, hFext_perm⟩
```

The old arbitrary-permutation pseudocode using
`bvt_F_extendF_perm_edgePairing_eq_from_OS`,
`BHW.jostWitness_exists_for_perm_overlap`, and
`BHW.isConnected_permForwardOverlapSet_for_perm` is no longer the primary
route.  Those names ask for all-permutation real overlap data and are too
strong as construction targets.  The primary construction is adjacent edge data
plus the PET monodromy theorem
`BHW.extendF_pet_branch_independence_of_adjacent`.

Primary boundary-level closure:

```lean
private theorem bvt_locally_commutative_boundary_route_of_two_le
    (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsep hswap
  have hEdge : SelectedAdjacentPermutationEdgeData OS lgc n :=
    bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le
      (d := d) hd OS lgc n
  obtain ⟨Fext, hFext_holo, hFext_agree, hFext_lorentz, hFext_perm⟩ :=
    bvt_F_symmetric_PET_extension_of_adjacentEdgeData (d := d) OS lgc n hEdge
  exact
    bv_local_commutativity_transfer_of_symmetric_PET_boundary
      (d := d) n
      (bvt_W OS lgc n)
      (bvt_F OS lgc n)
      Fext
      (bvt_F_holomorphic (d := d) OS lgc n)
      (bvt_boundary_values (d := d) OS lgc n)
      hFext_holo
      hFext_agree
      hFext_lorentz
      hFext_perm
      i j f g hsep hswap
```

The unqualified theorem-2 closure must now be a case split.  The `2 ≤ d` case
uses `bvt_locally_commutative_boundary_route_of_two_le`.  The `d = 1` case must
use one of the two explicitly documented non-circular routes:

```lean
private theorem bvt_locally_commutative_boundary_route_of_one
    (OS : OsterwalderSchraderAxioms 1)
    (lgc : OSLinearGrowthCondition 1 OS) :
    IsLocallyCommutativeWeak 1 (bvt_W OS lgc) := by
  -- Route 1: produce a genuine d=1 real-open adjacent edge packet and reuse
  -- the selected-adjacent/PET boundary route; or
  -- Route 2: use a d=1 complex-edge OS45/EOW boundary theorem directly.
  -- This proof may cite the validated d=1 BHW blockers only after their
  -- hypotheses are non-circular for the selected OS family.  In particular it
  -- must not supply `hF_local_dist` with the target theorem itself.
```

Do not call the `2 ≤ d` real-edge packet under only `[NeZero d]`; that would
reintroduce the false real adjacent-seed assumption.  Also do not represent a
complex-edge-only `d = 1` argument as a proof of
`SelectedAdjacentPermutationEdgeData` unless it really constructs the required
real-open `V` with the two real ET fields and compact-test edge equality.

Fallback finite-height closure, only if the current private consumer is kept:

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- All BHW/EOW, open-edge, boundary-continuity, and canonical finite-shell work
  -- is below this frontier theorem. This proof should only consume the
  -- completed arbitrary-transposition finite-shell pairing theorem.
  exact
    bvt_F_swapCanonical_pairing_from_transposition_pointwise
      (d := d) (OS := OS) (lgc := lgc) n i j f g ε hε hsep hswap
```

## 12. Fallback regular-input constructor theorem

This section is retained as a fallback-route audit.  It is useful if we later
decide to prove raw boundary continuity, but it is not part of the primary
OS-I-faithful theorem-2 path.  The primary path runs through
`bvt_F_distributionalEOW_permBranch_from_euclideanEdge`,
`bvt_F_hasPermutationEdgeDistributionEquality`, and the BHW `extendF`
real-Jost edge theorem.  The `bvt_W_perm...` theorem is a compatibility
adapter, not the main bridge.

For the fallback continuity route, the blueprint should still be explicit about
one important fact:

```lean
SCV.hasFourierLaplaceReprRegular_of_boundary_and_growth
```

does **not** exist anywhere in the current repo.

What *does* exist is the downstream package that *consumes*
`HasFourierLaplaceReprRegular`:

1. `boundary_function_continuous_forwardTube_of_flatRegular`,
2. `boundary_value_recovery_forwardTube_of_flatRegular`,
3. `distributional_uniqueness_forwardTube_of_flatRegular`,
4. `polynomial_growth_forwardTube_of_flatRegular`.

So the fallback route should be documented as requiring a new constructor
package, not as a one-line application of an already-existing helper.

The honest fallback theorem-slot inventory is:

```lean
lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap)

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma flatRegular_of_boundary_distribution_and_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
```

The first two are already the theorem shapes the blueprint was using. The third
is the real missing theorem. Only the fourth is an adapter name specialized to
`bvt_F`.

### 12.1. What the constructor proof must look like

The later Lean proof should be documented as:

1. prove holomorphy of the flattened function from `bvt_F_holomorphic`,
2. prove distributional boundary values of the flattened function using the
   existing `bvt_W` boundary package,
3. prove polynomial growth on the flattened tube from the already-constructed
   growth package for `bvt_F`,
4. package those three inputs into a new regular constructor theorem,
5. only then call the forward-tube continuity/recovery theorems.

The critical point is that Step 4 is a real theorem package, not a missing
`simpa`.

### 12.2. Estimated Lean line counts for the regular package

1. flattened boundary-value adapter:
   roughly `25-60` lines.
2. flattened growth adapter:
   roughly `20-50` lines.
3. regular constructor theorem
   `flatRegular_of_boundary_distribution_and_polyGrowth`:
   roughly `60-120` lines if done directly in the flattened SCV language.
4. specialization to `bvt_F_hasFlatRegularRepr`:
   roughly `10-25` lines.

So the honest continuity package here is roughly `115-255` lines, and the
central missing theorem is the regular constructor, not the continuity theorem
itself.

## 13. Correct selected-pair support rewrite

The support hypothesis for the public theorem is still used pointwise, but it
must be rewritten into reduced coordinates rather than upgraded to absolute
extended-tube membership.

The public proof should proceed as follows.

1. During the finite-shell adapter, after the swap change of variables, reduce
   the two absolute shell values through
   `bvt_F_eq_bvt_F_reduced_reducedDiffMap`.
2. Rewrite the reduced real base point by
   `BHW.reducedDiffMapReal (m + 1) d x`.
3. Use `reducedPairDiff_reducedDiffMapReal` to turn the production support
   hypothesis
   `AreSpacelikeSeparated d (x i) (x j)` into the reduced local-edge hypothesis
   for `reducedPairDiff m i j ξ`.
4. Apply
   `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`.
5. Return to the absolute shell statement using the reduced-direction lemmas.

In Lean-style pseudocode:

```lean
theorem reducedPairDiff_reducedDiffMapReal
    (m : ℕ) (i j : Fin (m + 1)) (x : NPointDomain d (m + 1)) :
    reducedPairDiff (d := d) m i j
        (BHW.reducedDiffMapReal (m + 1) d x)
      =
      fun μ => x j μ - x i μ := by
  -- Expand the real difference-coordinate section.  The common basepoint
  -- translation cancels from the pair difference.

theorem bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) →
      bvt_F OS lgc n
        (permutedEtaCanonicalShellOfPerm (d := d) n (Equiv.swap i j) x ε)
      =
      bvt_F OS lgc n (canonicalShell (d := d) n x ε) := by
  -- handle `n = 0` by `Fin n` elimination;
  -- set `m := n - 1` and identify `n` with `m + 1`;
  -- factor both sides through `bvt_F_reduced`;
  -- use the canonical/permuted reduced-direction lemmas;
  -- rewrite spacelike separation with `reducedPairDiff_reducedDiffMapReal`;
  -- apply the reduced local-edge theorem.
```

The adjacent `choose_real_open_edge_for_adjacent_swap` package may remain as a
pilot for raw-boundary arguments, but it is not the public selected-pair
finite-shell route.  In particular, do not add a theorem claiming that one
selected spacelike pair implies absolute `ExtendedTube` membership for
`realEmbed x` and `realEmbed (x ∘ Equiv.swap i j)`.

## 14. Exact proof sketch for the finite canonical-shell adapter

The adjacent theorem

```lean
bvt_F_adjacentSwapCanonical_pairing_from_pointwise
```

should not be left as a slogan.  More importantly, the public theorem needs the
general-transposition analogue

```lean
bvt_F_swapCanonical_pairing_from_transposition_pointwise
```

The later Lean proof should make this a named finite-shell adapter.

1. rewrite the left pairing using
   `hswap : g x = f (fun k => x (swap k))`;
2. change variables by the `Equiv.swap i j` coordinate permutation, using the existing
   product-volume measure-preserving reindexing theorem;
3. reduce the integrand equality to the pointwise finite-shell statement
   `bvt_F_swapCanonical_pointwise_of_spacelike`;
4. use the support hypothesis only on `tsupport f`; outside `tsupport f`, the
   `f` factor kills the integrand.

The theorem-slot inventory should therefore be:

```lean
theorem canonical_adjacentSwap_shell_mem_EOW_domain
lemma swappedCanonicalShell_eq_perm_permutedEtaCanonicalShell
theorem bvt_F_permutedEtaCanonicalShell_eq_canonicalShell_of_spacelike
theorem bvt_F_adjacentSwapCanonical_pointwise_of_spacelike
theorem bvt_F_adjacentSwapCanonical_pairing_from_pointwise
def bvt_F_reduced
theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
theorem canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC
theorem permutedCanonicalForwardDirection_reducedDiff_eq
theorem reducedDiffMap_canonicalShell_eq
theorem reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq
theorem reducedPairDiff_reducedDiffMapReal
theorem bvt_F_reduced_permOnReducedDiff
theorem permOnReducedDiff_swap_permutedCanonicalDirection
theorem bvt_F_reduced_permutedDirection_to_realPermutedCanonical
theorem bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike
theorem bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike
theorem bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike
theorem bvt_F_swapCanonical_pointwise_of_spacelike
theorem bvt_F_swapCanonical_pairing_from_transposition_pointwise
```

Estimated Lean size:

1. reduced algebraic shell packet:
   `110-210` lines, mostly definitional expansions of `reducedDiffMap`,
   `safeSection`, `permOnReducedDiff`, and permutation bookkeeping;
2. reduced canonical-real-swap local-edge theorem:
   still unestimated; this is the current hard analytic statement, now reduced
   to canonical imaginary direction and a selected real reduced-basepoint swap;
3. adjacent permuted-eta finite-shell theorem:
   `30-80` lines after the adjacent EOW-domain membership and analytic
   uniqueness surface are available;
4. adjacent pointwise finite-shell theorem:
   `20-60` lines after the EOW-domain membership theorem exists;
5. adjacent pairing adapter from pointwise equality:
   `25-60` lines, mostly measure-preserving reindexing and support-zero
   bookkeeping;
6. arbitrary-transposition pointwise finite-shell theorem:
   `30-90` lines after the reduced local-edge theorem and reduced shell packet
   exist;
7. general transposition pairing adapter:
   `30-70` lines after the pointwise theorem exists, mostly the same
   measure-preserving reindexing and support-zero bookkeeping as the adjacent
   adapter.

So the theorem-2 endgame is reduced finite-shell first: reduced-coordinate
factorization, reduced local-edge comparison, absolute pointwise shell
interchange, pairing integration, and then the direct general-transposition
adapter.

## 15. The forward-Jost / absolute-ET subtlety must stay explicit

The locality blueprint should keep one geometry subtlety visible:

1. `ForwardJostSet d n hd` is defined by a condition on every consecutive
   difference.
2. Absolute `ExtendedTube d n` is likewise a global condition on the whole
   configuration, expressed through the BHW orbit of the forward tube.
3. The theorem-2 locality hypothesis only names one selected pair of indices.
4. Therefore selected-pair spacelike separation is not enough, by itself, to
   put the whole real configuration or its selected transposition in the
   absolute forward-Jost/extended-tube geometry.

This matters most visibly in low-dimensional examples, but it is a general
theorem-shape issue.  The route should not hide it behind convenient names.

### 15.1. What is safe to claim

The docs may safely claim:

1. if the support is already known to lie in an open edge `V` with the required
   ET and swapped-ET embeddings, that edge can feed raw-boundary or adjacent
   pilot arguments;
2. if a stronger support theorem is separately proved that upgrades the
   locality support hypothesis to `ForwardJostSet` membership, then
   `forwardJostSet_subset_extendedTube` can close that stronger route;
3. the fallback finite-shell route does not need either global forward-Jost
   membership or absolute ET-overlap from one pair, because it uses reduced
   difference coordinates and a reduced local-edge theorem;
4. boundary-value recovery identifies the limiting raw boundary distribution;
   it does not replace the finite-shell pointwise interchange proof needed at
   fixed `ε > 0`.

### 15.2. What is not safe to claim

The docs should not claim, without a new stronger hypothesis:

1. one selected-pair spacelike-separation hypothesis automatically implies
   `ForwardJostSet` membership on the whole support;
2. one selected-pair spacelike-separation hypothesis automatically implies
   absolute `ExtendedTube` membership for `realEmbed x`;
3. one selected-pair spacelike-separation hypothesis automatically implies
   absolute `ExtendedTube` membership for
   `realEmbed (fun k => x (Equiv.swap i j k))`;
4. a bubble-sort chain of adjacent swaps is valid under a hypothesis that only
   controls the original selected pair;
5. the `d = 1` case is merely a cosmetic special case of the same argument.

### 15.3. Honest theorem-slot split

The later Lean port should separate three possible routes.

#### Route A: stronger forward-Jost support theorem

```lean
lemma support_mem_forwardJost_of_swap_spacelike
    (f : SchwartzNPoint d n) (i j : Fin n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) :
    ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      x ∈ ForwardJostSet d n hd
```

This is a fallback strengthening only.  It is strongest, but also most
delicate, because the conclusion is about all consecutive differences.

#### Route B: adjacent open-edge pilot

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) ∧
      (∀ x ∈ V,
        BHW.realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
          BHWCore.ExtendedTube d n)
```

This route may remain useful for adjacent raw-boundary statements and for
testing the BHW edge machinery.  It is not the public selected-transposition
finite-shell route.

#### Route C: fallback reduced finite-shell route

```lean
theorem bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (m : ℕ) (i j : Fin (m + 1))
      (ξ : NPointDomain d m) (ε : ℝ), 0 < ε →
      MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) →
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
                Complex.I))
      =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)
```

This is the honest fallback route if we deliberately keep the current private
finite-height consumer `bvt_F_swapCanonical_pairing`.  It expresses the
selected-pair seam in reduced coordinates, with the imaginary direction
normalized back to the canonical one.  It is no longer the recommended first
route to theorem 2, because the BHW/PET boundary route can prove locality by a
more direct permutation-edge theorem for `extendF`.

### 15.4. Recommended implementation order

After the #1065 route audit, the next Lean implementation must start with the
OS-internal edge supplier, not PET monodromy.  The immediate proof-doc-to-Lean
order is:

1. finish the Lean-ready transcript for
   `bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le`;
2. implement/check the adjacent real-open edge geometry in the `2 ≤ d` range:
   `choose_real_open_edge_for_adjacent_swap`, ET membership, swapped-ET
   membership, nonemptiness, and adjacent overlap connectedness;
3. implement/check the test-function preparation:
   `BHW.permuteZeroDiagonalSchwartz`, support transport, compact support
   transport, `BHW.jostSet_disjoint_coincidenceLocus`, and
   `zeroDiagonal_of_tsupport_subset_jostOverlap`;
4. prove the Euclidean branch-pairing equality from E3 and
   `bvt_euclidean_restriction`;
5. prove the corrected ACR/EOW/BHW transport theorem that turns the Euclidean
   pairing equality into the real-Jost `extendF` compact edge equality, using
   the OS §4.5 common analytic continuation and Jost boundary theorem rather
   than local Lorentz orbit witnesses for point permutations;
6. package these results as
   `bvt_F_selectedAdjacentPermutationEdgeData_from_OS_of_two_le`.

For the unqualified `[NeZero d]` theorem, do **not** insert a vaguely named
`d = 1` complex-edge supplier into step 6 unless it actually fills the
real-open fields of `SelectedAdjacentPermutationEdgeData`.  Instead, split the
proof by dimension:

1. `2 ≤ d`: implement steps 1-6 exactly as the real-open OS45 adjacent-edge
   packet.
2. `d = 1`, real-open variant: first prove a dedicated theorem constructing
   the actual `SelectedAdjacentPermutationEdgeData.edge_witness` fields in
   dimension one, then reuse the adjacent-edge/PET route.
3. `d = 1`, complex-edge variant: bypass `SelectedAdjacentPermutationEdgeData`
   and prove `bvt_locally_commutative_boundary_route_of_one` directly from the
   dimension-one OS45/EOW boundary packet.

The existing validated `PermutationFlowBlocker.lean` blockers are downstream
BHW/permutation-flow trust surfaces.  They may support a later BHW endgame, but
they must not be used in the non-circular theorem-2 proof while their
hypotheses include the target locality statement.

Only after that packet exists should the implementation return to the BHW/PET
boundary route:

1. prove/export the adjacent branch-envelope theorem for the selected `bvt_F`;
2. export arbitrary-permutation branch independence through the BHW/PET
   permutation-flow or germ-chain spine;
3. build the symmetric PET boundary package;
4. add the boundary-transfer theorem that proves
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)` from this PET boundary package.

Route C should be implemented only if that primary route is blocked or if we
choose to retain the current overstrong finite-shell consumer.

1. Implement the reduced algebraic packet:
   `bvt_F_reduced`, reduced factorization through `reducedDiffMap`, direction
   reduction for canonical and permuted-canonical shells, and
   `reducedPairDiff_reducedDiffMapReal`.
2. Implement the reduced permutation algebra:
   `bvt_F_reduced_permOnReducedDiff`,
   `permOnReducedDiff_swap_permutedCanonicalDirection`, and
   `bvt_F_reduced_permutedDirection_to_realPermutedCanonical`.
3. Finish or further document the reduced local-edge theorem
   `bvt_F_reduced_canonicalRealSwap_eq_of_pairSpacelike`.
4. Derive
   `bvt_F_reduced_permutedCanonicalDirection_eq_canonical_of_pairSpacelike`
   from the reduced permutation algebra and canonical-real-swap theorem.
5. Prove the absolute adapter
   `bvt_F_permutedEtaCanonicalShellOfSwap_eq_canonicalShell_of_spacelike` by
   factoring both sides through the reduced theorem.
6. Prove `bvt_F_swapCanonical_pointwise_of_spacelike` using `bvt_F_perm` and
   the shell algebra.
7. Prove the pairing theorem by swap change-of-variables and support-zero
   bookkeeping.

Route B can be kept as an adjacent pilot, but should not block the primary
BHW/PET boundary route.  Route A should only be revived if the stronger
forward-Jost theorem is genuinely proved under the current theorem surface.

### 15.5. Estimated Lean size after the correction

1. Reduced algebraic packet:
   `110-210` lines, mostly definitional calculation, `safeSection`
   bookkeeping, and existing `DifferenceCoordinatesReduced` permutation
   lemmas.
2. Reduced canonical-real-swap local-edge theorem:
   not yet line-estimated; this remains the single hard analytic seam.
3. Reduced permuted-direction adapter:
   `20-50` lines after the reduced permutation algebra compiles.
4. Absolute finite-shell adapter from the reduced theorem:
   `30-90` lines after the reduced packet compiles.
5. Pairing adapter:
   `30-70` lines after the pointwise shell theorem exists.

The docs should therefore treat the branch-envelope theorem and the local
distributional Wick-section identity as the next proof-doc gaps for the primary
route.  The reduced canonical-real-swap local-edge theorem is the next gap only
on the fallback finite-shell route.
